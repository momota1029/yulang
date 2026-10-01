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

#### Finite source-origin superset for callable bodies

Frozen-Oracle executable IR suggests a finite *body-origin* superset without
defining how a method, role, or implementation is selected. For one frozen
executable mono program `P` and its successfully lowered control-IR form, let
`Body(P)` contain every user body entry in its finite instance table and every
lambda body expression in its finite expression graph. Let `Prim(P)`,
`Ctor(P)`, and `Op(P)` contain the finite primitive-operation, constructor,
and operation-path producer sites. Treat imported/client/host-supplied
callables without a closed body summary as `ExternalTop`; represent captured
continuations through the continuation slots instead of pretending each
runtime continuation is a source body. The candidate body-origin universe is:

```text
Origin(P) = Body(P) ∪ Prim(P) ∪ Ctor(P) ∪ Op(P) ∪ {ExternalTop, KontTop}
```

The source characterization is based on the frozen Oracle at `a58eefc3`:
`control_ir::Program` stores finite `exprs` and `instances`, and its `Expr`
variants include `Lambda`, `InstanceRef`, `PrimitiveOp`, `Constructor`,
`EffectOp`, `FunctionAdapter`, `MakeThunk`, and the value/container/control
forms. `mono-runtime::eval_expr` creates closures, primitive/constructor/op
values, adapters, and thunks from those static expression nodes. Its
`apply_value` dispatches marked values to their wrapped value, adapters to
their underlying function, and thunks through force; continuations take the
captured-resumption path. Recursive closure calls re-enter a finite source
body rather than inventing another body site. The source locators are
`crates/control-ir/src/ir.rs:1-105`,
`crates/mono-runtime/src/runtime/eval.rs:1-124`, and
`crates/mono-runtime/src/runtime/flow.rs:1-31,72-130` in that checkout.

Conditional coverage lemma: for any execution of this frozen `P`, every local
user-body
entered by an application has an origin in `Body(P)`; a primitive,
constructor, or operation value has an origin in its corresponding finite
producer set; an adapter preserves its wrapped body-origin set; and forcing a
local thunk can reveal only origins already in `Origin(P)`. External values
without closed summaries map to `ExternalTop`, and captured continuation calls
map to `KontTop` or a separately proved continuation slot. Proof is by
induction over value construction and application: static producer cases add
only their own finite site; locals and container/select/case/block paths
reuse a previously constructed value; adapters retain the wrapped origin
while keeping hygiene evidence separate; thunk force evaluates an existing
finite expression body; runtime `adapt_value` wrappers retain their underlying
callable origin; callable results returned by a primitive retain the origin of
the value they return; and recursion reuses a member of `Body(P)`. Since the
source tables and expression graph are finite, `Pow(Origin(P))` is a finite
abstract target domain.

This proves target-origin coverage only. It does not prove that a target is
reachable at a particular call, that a request reaches a particular handler,
that an adapter's boundary grants eligibility, or that a family may be
subtracted. The across-assignment premise `Lift(S)` has a source-level
candidate for a fixed finite source closure `S`: let `BodySrc(S)` be its
finite set of module-qualified named `DefId`s and source-arena-qualified
`PolyExprId`s whose expression is a lambda. Both frozen specialization paths
emit a mono lambda only at the `PolyExpr::Lambda` case
(`specialize/src/lib_support/specializer.rs:204-212`,
`specialize/src/specialize2/emit.rs:268-277`); the boundary adapter helper
that matches a mono lambda copies its existing parameter/body rather than
creating another body (`specialize/src/lib_support/boundary.rs:175-183`).
The second path's marker traversal likewise rewrites an existing lambda by
recursing over its current parameter/body and does not synthesize a new body
(`specialize/src/specialize2/marker.rs:145-205`).
Every generated mono instance records `InstanceSource::Def` at allocation
(`specializer.rs:147-164`; `specialize2/emit.rs:196-205`). Mono-to-control
lowering preserves those source bodies and lambda expressions
(`control-ir/src/lower.rs:113-184`). Therefore each local function body in
every successful specialization maps to a member of `BodySrc(S)`, regardless
of how many type/effect assignments produce instances. This closes `Lift(S)`
for local named and lambda body origins under the frozen lowering paths and
the fixed-source/no-dynamic-code premise; a complete import closure must be
included in `S`, while bodyless imported or host values still map to
`ExternalTop`. The mapping for generated lambdas is an existential provenance
relation through lowering: frozen mono/control IR does not retain the source
`PolyExprId` on each lambda. An implementation that needs to look up that key
must carry a separate source-origin map; this proof does not claim the ID is
currently recoverable from the executable IR alone.

This remains an origin-universe result, not a call-site target analysis. A
source route analysis may use a smaller target set only after proving it
contains all targets under every admissible type assignment; otherwise its
safe local fallback is the broad `BodySrc(S)` set, with `ExternalTop` and
continuation slots added where applicable. In particular, the body-origin key
shares neither effect-family identity nor hygiene/path evidence: adapters
keep separate ordered boundary evidence, and polymorphic effect arguments
require their own binder substitution or `TopFam` when that set is not finite.
This is Oracle executable-shape characterization and a candidate abstraction
lemma, not authority for Oracle's selection or weight rules, not a start of
the later selection-semantics gate, and not yet a source-to-constraint proof.
Its final-acceptance cost remains unmeasured.

A focused compiler-referee review found no blocking or major counterexample
for one frozen executable program. It confirmed the runtime callee cases and
required the present scope: `P` includes mono-to-control lowering, host-supplied
callables map to `ExternalTop`, and the then-open cross-assignment `Lift(S)`
proof remained outside its review. The separate `Lift(S)` delta review found
no blocking/major counterexample; it required the marker-wrapper citation and
the existential-provenance limitation now stated above. Call-specific
reachability, handler routes, adapter eligibility/hygiene, and effect-family
substitution remain outside both reviews.

#### Candidate source-origin transport across specialization

The frozen specialization audit supports a finite *relation*, not a
recoverable one-to-one identity map, from emitted runtime expression and
pattern sites to stable source origins. For a fixed finite checked source/import
closure `S`, let `SrcOrigin(S)` contain arena-qualified source expression
`ExprId`s, arena-qualified source pattern `PatId`s, module-qualified source
`DefId`s, and explicit `UnknownOrigin` and `ExternalTop` elements. A side
relation `OriginOf_S(site) ⊆ SrcOrigin(S)` maps each expression or pattern execution
site to all source origins that could have produced or be executed through
it. Every ordinary emitted expression inherits the source
expression currently being traversed; each emitted instance body also maps
to its source definition. A generated node may carry the triggering source
site plus any separately executed generated body. For example, a generated
cast `Apply` must include the cast `DefId` as a possible body origin, not only
the adapted source expression (`specialize2/emit.rs:1029-1068`). If a
generated constructor or rewrite has no proved owner, map it to
`UnknownOrigin`; bodyless imported or host code maps
to `ExternalTop`. `UnknownOrigin` is not an inert singleton target: its
concretization contains every source body and producer origin in `S`, plus
external and continuation origins. Any value containing it widens to
`TopValue`; projecting, calling, forcing, adapting, or routing that value uses
the full top transfer, including `⊤Eff`, `TopKont`, and top request/blocker
observations at every compatible handler destination. Thus it cannot produce
positive `Drop` evidence. `ExternalTop` has the same conservative transfer
unless a closed external summary is separately proved.

Both frozen emitters recursively lower source expressions, lambda bodies,
aggregates, spreads, guards, and pattern defaults
(`specialize/src/lib_support/specializer.rs:173-287,434-466,621-710`;
`specialize/src/specialize2/emit.rs:233-372,479-509,559-614,706-763`), and
instance allocation retains its source definition
(`specializer.rs:95-153`; `emit.rs:167-205`). Mono-to-control lowering
traverses these occurrences (`control-ir/src/lower.rs:109-261,319-345`).
This gives the relation a finite codomain across successful
specializations even when instance counts and mono IDs differ. However, the
current executable artifacts do not carry this total relation: the newer
emitter records only sparse application/selection provenance
(`emit.rs:340-362`; `mono/src/lib.rs:176-243`), the legacy emitter creates
untagged nodes (`specializer.rs:276`), control lowering transports only those
sparse tags (`lower.rs:237-260`), and marker rewrites recreate nodes while
restoring only application and selection tags (`specialize2/marker.rs:145-263`).
Therefore an analysis that needs `OriginOf_S` must instrument both emitters,
every generated wrapper/rewrite, and control lowering with a side table, or
conservatively widen unaccounted nodes to `UnknownOrigin` and the corresponding
whole value/effect/control fact to top.
This is a finite-relation construction target, not an implementation already
present in the Oracle and not yet a proof that every generated node has been
accounted for. In particular, it does not define method/role/implementation
selection; generated cast bodies are included only as an explicit target
dependency of the adaptation site.

A read-only audit of both frozen emitters and the mono-to-control and marker
passes supports this bounded characterization. It found no total source
identity in the existing IR and confirmed the generated-cast body exception.
The exact source relation still needs implementation and source-step simulation
review.

A constructor-site sweep at frozen `a58eefc3` now narrows that remaining
coverage obligation. All production `mono::Expr::new` sites in the two
specialization paths are in legacy `lib_support/{specializer,boundary}.rs`
and new `specialize2/{emit,runtime_shape,marker}.rs`; no direct `mono::Expr`
struct construction appeared. Ordinary recursive emission is attributed to
the current arena-qualified `PolyExprId`, and instance bodies to their source
`DefId`. Force/thunk/adapter/coerce wrappers inherit the wrapped expression's
origin and its source root, statement, or body trigger. Marker rewrites copy
the replaced node's origin; inserted `MarkerFrame`s carry their wrapped body
and enclosing instance origin, or `UnknownOrigin` if that relation was lost.
Control lowering creates one control expression per mono expression and
traverses pattern defaults.

The audit also widens the target relation beyond expression constructors:
variable and method/typeclass selection, and pattern references, can enqueue
executable instances without a new expression node. When the actual runtime
instance body is known, pair its `DefId` with the triggering expression or
pattern origin. A source `DefId` alone is insufficient for the new emitter's
bodyless `PolyPat::Ref` branch: it constructs
`Pat::Ref(InstanceId(convert_def(def).0))` without allocating an instance
(`specialize2/emit.rs:527-545`), while runtime pattern matching evaluates that
numeric instance ID (`mono-runtime/src/runtime/bind.rs:82-85`). If the target
cannot be proved to name the intended body, the pattern execution site maps to
`UnknownOrigin` and takes the whole top transfer. Thus the relation includes
an explicit pattern-match event edge, not only expression nodes. A generated
cast `Apply` similarly carries both its adapted-expression trigger and its
cast-rule `DefId`. This is only runtime-origin coverage; it does not define
selection semantics, and unresolved selection stays top until the later
mandatory method/role/implementation gate. The sweep supports a finite total
relation with the stated fallback, conditional on carrying these labels
through every emission and rewrite. It does not prove that this instrumentation
has been implemented or that the resulting abstract transitions simulate all
source steps.

#### Conditional ghost-origin erasure for pattern-reference binding

For one fixed frozen executable, add the `PatSite` to each pattern-reference
bind continuation. The side origin map must retain the source arena-qualified
`PatId`; the runtime `Pat::Ref(InstanceId)` alone does not retain it. If the
actual allocated instance body is proved, carry its `DefId` too. The
bodyless-reference fallback remains `UnknownOrigin`/top.

Conditional erasure claim: with the same raw pattern, environment, instance
cache, and bind continuation, adding this ghost `PatSite` and origin metadata
does not change the Oracle transition or error. The bounded case audit is:

| Raw path | Erasure condition |
|---|---|
| Match `Pat::Ref(instance)` | Tagged matching carries `PatSite` beside the same raw `InstanceId`; the runtime still calls `eval_instance`, then compares the same raw values with `value_equivalent`. Erase tags before raw equality. |
| `eval_instance` cache hit or miss | Keep the same `InstanceId`, cache/cycle state, body, and empty evaluation environment. Cache marker stripping sees the same raw value; body origin is side metadata only. |
| Instance body returns a `Request` | Preserve the same `expect_eval_value` conversion to `UnhandledEffect`. The request does not continue through the pattern bind callback or get dispatched by that binding path. This is frozen runtime behavior, not a successor effect rule. |
| Bind continuation returns `Done` or `BindRequest` | Carry the same callback and raw environment; ghost pattern metadata is stored alongside the callback and erased before invoking the raw callback. Any record-default evaluation that precedes a nested reference remains its own expression step and request path. |

This gives only tag erasure for the `Pat::Ref`/instance-evaluation binding
path, conditional on the exact raw cache/body/environment premises. It does
not prove that the source site maps to the right runtime instance, that
captured markers and defaults are covered by the finite value relation, or
that the full source/runtime step simulation holds. The source inventory is
`mono-runtime/src/runtime/bind.rs:82-85,91-123,170-189,191-271`,
`mono-runtime/src/runtime/engine.rs:67-92`,
`mono-runtime/src/lib.rs:667-671,1219-1223`, and
`mono-runtime/src/runtime/thunk.rs:182-211,238-260` in frozen `a58eefc3`.

#### Candidate source-level value-flow closure

The finite origin set can feed a row-independent inclusion analysis rather
than assigning every local body to every call. For a fixed finite source
closure `S`, define finite `Slot(S)` keys for expression results, definitions
and parameters, tuple positions, record fields, reference cells, thunk results,
lambda captures, call arguments/results, handler results, and continuation
sites. Let `Pt : Slot(S) -> P(Origin(S))`, where `Origin(S)` uses `BodySrc(S)`
and the primitive/constructor/operation origins already defined above. The
finite value domain must also have a distinct `TopValue`, meaning an arbitrary
value with arbitrary nested callable fields; projection, destructuring,
forcing, or application of `TopValue` stays top unless a sound shape summary
proves otherwise. Every unconstrained value entering through an exported
parameter or bodyless imported/host interface is seeded with `TopValue`,
including aggregate parameters whose nested fields may contain client-supplied
callbacks. A narrower seed requires a sound shape summary for that interface.
Unknown patterns, open record spreads,
unresolved references, or unmodelled interface edges widen the affected slot
to top; they must not be treated as empty.
Seed analysis from every runtime root and every exported function entry, with
all of its externally supplied parameter values seeded as above under the
permitted client contexts.

The proposed transfer is the least closure of positive inclusion edges:

| Source form | Candidate value-flow transfer |
|---|---|
| literal / primitive / operation / constructor | literal adds no callable origin; the other forms add their finite producer origin |
| resolved variable or local binding | copy the referenced definition slot to the expression result |
| lambda / named definition | add the source body origin; copy captured environment slots into closure capture slots |
| tuple / record / variant | copy each element into its finite position/field slot; spreads union known fields or widen unknown fields; projecting `TopValue` gives `TopValue` |
| pattern / case / block | recursively project aggregate slots into bound definitions; union possible branch/tail results; let and ref reads/writes use version-insensitive cell slots; `Or`/`As` patterns union/copy; list-shape uncertainty widens binders to top |
| record-pattern default / guard | include each default's value and effect even when it is conditionally executed; include guard effects and all arm result alternatives |
| application of a known body origin | flow the argument into its formal slot and the body result into the application result; recursive edges use the same finite slots |
| thunk / force | flow the thunk body's result into the force result; transfer its latent-effect slot into immediate effects only at force |
| adapter | preserve the wrapped target set and attach ordered adapter-boundary evidence in a separate slot |
| selection | use a target only if uniform across assignments; otherwise include all finite local origins, or top for open registries; projecting `TopValue` remains top |
| catch / continuation | union value/arm results; assign each continuation a finite source slot and use top when captured control cannot be represented; keep raw/forwarded route tags separately |

`App` must also dispatch producer-specific rules. In particular, an operation
origin application produces a thunk with a latent request effect; it does not
by itself emit the request. Offer facts arise when that thunk is forced (or
implicitly forced), under the captured boundary/marker context. Continuation
application likewise produces a continuation thunk; its resumed effects and
re-entry route arise on force. Constructor application packages its argument
slots; known primitives use a proved finite value-shape summary (including
origins carried inside returned arguments), while an unmodelled primitive
result widens to `TopValue`. This is needed for primitives such as indexing
that can return a callable stored in an input aggregate. Until its protocol is
proved, `RefSet` also uses the conservative unknown-call rule: the runtime path
projects and invokes `update_effect`, so a cell-write edge alone does not
cover its effects or returned value. An unknown or external callee adds
`⊤Eff`, `Unknown` route/blocker facts, and top value/continuation flow at every
active or exported handler slot in scope.
Handler coverage metadata remains separate and seeds no offer. Adapter target
identity, binder substitution,
boundary history, and handler visibility are distinct components; joining
`Pt` sets must not merge their evidence.

For finite `Slot(S)` and `Origin(S)`, `Pt` plus the one `TopValue` element is a
finite product of powersets. If each `Pt` transfer is a fixed inclusion edge,
its closure operator is monotone, so the least fixed point exists and is
reached after finitely many strict increases. This lfp claim is only for
value-origin facts. It does not include handler scope, ordered adapter history,
route evidence, or effect rows. Those components may have unbounded recursive
histories and need a separately proved finite quotient and monotone coupling
before a joint fixed point can be claimed. The transfer table is not yet
executable or complete: source-step simulation must cover stores, nested
aggregate projections, conditional defaults, guards, callback escape/re-entry,
selection fallback, thunk force, handler arms, and resumed continuations. Then
prove a concretization relation mapping every dynamic callable and latent
effect to `Pt` plus route evidence. Until that simulation closes, the least
points-to solution is not a sound `Drop` certificate or a principal effect
solution. The universal source-origin set remains the fallback for unresolved
local dispatch; its acceptance cost still needs measurement.

#### Conditional state-closed request-origin envelope

The finite origin/value-flow candidate gives one way to close the resumption
state premise for *support*, without counting continuation uses. For a fixed
finite source closure `S`, let `ReqSite(S)` be the finite operation-producer
sites in `Origin(S)` and let `Slots(S)` be the finite value/call/force/
continuation slots above. A request template retains its producer site,
resolved `OpId` when known, symbolic family-argument tuple, payload/result
types, and source/use owner; an open argument, operation target, or owner is
represented by the corresponding unknown top fact rather than erased.

Combine the value-flow edges with request-origin propagation in one finite
product powerset lattice. Entering a known body origin exposes that body's
request templates; forcing a known thunk exposes its stored body or latent
templates; resuming a continuation exposes the templates attached to its
finite continuation slot. Any transition whose value, body, or continuation
target is `TopValue`/unknown contributes `TopEff` and `Unknown` request facts.
Handler arms contribute their own producer templates, while requests from the
raw continuation remain in its continuation slot. This transfer projects
request origins from the same evaluation relation; it adds no source-site
effect rule and does not authorize handler subtraction.

Formally, with a fixed finite template universe `ReqTpl(S)`, write the abstract
state as `X ∈ P(Slots(S)×Origin(S)) × P(ReqTpl(S))`. Let `Seed_S` contain all
module/runtime-root and exported/client-entry seeds, and let `F_S` be the
union of the table transfers plus the request-origin edges just described.
This fixed-point claim assumes those transfers are encoded as positive
inclusion edges (unknown cases widen, never filter), making `F_S` monotone.
The candidate solution is the Kleene least fixed point
`X* = ⋃_{n≥0} X_n`, where `X₀=Seed_S` and
`X_{n+1}=X_n ∪ F_S(X_n)`. Finiteness of both factors makes this sequence
stabilize. `E#` is the family-support projection of request templates in
`X*`; any unknown request fact maps it to `TopEff`. The route component is
deliberately not projected into a `Drop` decision by `E#`.

Assume every concrete source step that creates a callable, suspension,
operation request, or continuation is simulated by one of these finite slot
transfers, with capture-avoiding type/use ownership maps applied to the whole
request template and its `K_sym` incidence. The least fixed point then gives a
state-closed envelope for every finite execution prefix: by induction on
steps, a direct request comes from an included producer site; an application,
force, or resumption follows an included target/slot edge; and a store update
can change which existing branch or site is reached but cannot invent a new
producer origin. Repeated multi-shot resumes can revisit sites, but set
membership is idempotent, so no usage count is needed. Projection from request
templates to family support is consequently uniform over all live states
represented by the closure.

Because the transfer is monotone over a finite product of powersets, its least
fixed point is the least request-origin summary satisfying those abstract
edges, hence principal **within this origin-set abstraction**. This is not
leastness among exact trace supports or all typed row interfaces. Soundness
still depends on the unproved source-to-slot simulation, complete exported and
client-entry seeding, thunk/continuation capture coverage, and finite typed-use
ownership. If any of those is unknown, top is required. The family support
projection alone cannot carry `InvArgs`, payload/result coherence, or route
visibility; their formulas and incidence stay in `K_sym`/request facts through
solving, residualization, generalization, freshening, and intrusion. `Drop`
requires the separate handler visibility/coverage proof. This gives a
conditional finite state-closed bound, not yet an effective or Oracle-complete
effect inference machine.

Conceptual-economy constraint from the user: this product powerset is not a
second effect semantics and `ReqTpl` is not a new source-level construct or
obligation kind. It is admissible only as a finite presentation of the
existing coupled computation/interface relation: producer, slot, owner, and
edge IDs are solver indices; typed request meaning and handler visibility
remain observations of that relation. Calls, force, resumption, store
mutation, filtering, and handlers must be simulated by one source computation
relation, with the finite closure serving as its abstract reachable-interface
projection. Unknown targets may widen that projection to `Top`, but a handler
may remove support only through the relation's proved handler image/coverage.
The proof target is now a commuting abstraction diagram preserving symbolic
typed-family fibers through the existing relation operations and SCC
lifecycle. If the finite closure cannot preserve those fibers, that is a limit
of the presentation, not a reason to add source-site-specific semantics. See
`Finite request-origin closure as a presentation, not a second semantics` in
the coupled-effect draft.

#### Semantic coordinates versus presentation identities

The unified carrier is now stated modulo alpha-renaming of bound identities.
The semantics must preserve the equivalence relation saying which typed
request occurrences share a source binder, plus dynamic handler behavior.
Allocation-site, occurrence, owner-path, and route IDs are presentation
indices or proof witnesses; their literal identity is not observable. The
abstraction adequacy target is preservation of typed solution fibers and
handler transitions, not equality of instrumentation labels. This separates
the real semantics from the IDs used by the finite closure and transport
maps, while leaving source-to-presentation adequacy and finite principality
open. See the revised `One semantic carrier` section in the coupled-effect
draft.

#### Source-step correction: operation and continuation application are lazy

The frozen Oracle runtime's value-flow code sharpens the preceding transfer:
applying `Value::EffectOp` constructs `Thunk::Effect`; `force_thunk` emits the
request. Applying `Value::Continuation` constructs `Thunk::Continuation`, and
forcing it invokes the saved resumption. Therefore operation/continuation
application contributes a latent effect/value-flow fact, while direct offer
and resumed-route facts belong to force, implicit force, or continuation
re-entry. The thunk must retain the captured marker/boundary evidence when it
escapes the creating call. A candidate that emits an offer at the original
application site could falsely associate a later force with the wrong handler
activation and cannot authorize `Drop` until a captured-context simulation is
proved. The updated table records this split, based on `main` at `a58eefc3`,
`crates/mono-runtime/src/runtime/flow.rs::apply_value` and
`crates/mono-runtime/src/runtime/thunk.rs::force_thunk`. This is a correction
to the abstract transfer candidate, not a finding that the frozen runtime is
unsound; marker creation/closing, implicit force sites, and end-to-end
source/row coupling remain to be audited. Application evaluation still
includes the immediate effects of evaluating its callee and argument before
the producer-specific application step. Captured route evidence must model
marker transformations on wrapper calls and continuation resumes; a creation
site path alone is not a sufficient activation identity.

A bounded compiler-referee audit against the cited frozen runtime found no
major discrepancy in this lazy split. It confirmed that marked callables and
marked thunk forces route through marker frames, handler-frame closure wraps
returned values and request resumptions, and continuation calls/resumes apply
distinct marker transformations. This closes only the source locator and
transfer correction; it does not prove finite abstract route simulation or
permit positive `Drop` evidence.

#### Conditional thunk-step simulation cases

The local proof obligation can be stated without claiming a full source
simulation. For an exact abstract spine, relate an Oracle value/thunk to a
finite value slot plus its latent row, continuation reference, and captured
wrapper summary. A wrapper summary must retain the ordered marker transform
and the possible receiving-handler/boundary relations. If it cannot represent
the concrete activation relation, use `TopControl`/`TopKont`, not the
application site's handler identity.

| Exact runtime step | Required abstract successor and observation |
|---|---|
| Evaluate `Apply(callee, arg)`'s callee and argument | Simulate their evaluation steps first; retain any immediate effects/offers they produce. The producer-specific row below covers only applying the resulting values. |
| Apply an `EffectOp(path)` to its payload | Add an effect-thunk fact to the result slot with latent family/path and the marker transform on the returned value; emit no offer on this application step. |
| Apply a continuation | Add a continuation-thunk fact referencing the saved continuation/wrapper and its latent effect summary, plus the distinct continuation-call marker transform attached to the returned thunk; emit no resumed-suffix offer on this application step. |
| Force `Thunk::Expr` | Evaluate its stored body in its captured environment; simulate that body's steps, including any immediate effects/offers, and preserve its endpoint relation. |
| Force `Thunk::Value` | Return the stored value without adding an offer; transfer the stored value facts and latent rows to the result slot. |
| Force an effect thunk, including a marked thunk | Interpret its captured marker transform, emit a request observation before dispatch, and preserve the resulting request endpoint. If exact activation/scope/blocker labels cannot be represented, emit `TopObs` and retain top continuation/effect facts. |
| Force a continuation thunk | Invoke the represented saved continuation, preserve its raw/forwarded wrapper mode and endpoint, and recursively account for a thunk-valued resume result. If the saved continuation state is not exact, use `TopKont`/`TopControl` with `TopObs` on every possible request edge. |
| Force `Thunk::Adapter` | Recursively force its inner thunk, then transfer the result through the source/target adaptation; preserve any marker and nested latent-value evidence across both steps. |
| Implicit force (thunk callee, thunk adaptation, case scrutinee, or reference operation) | Reuse the same force transfer at that concrete force point; do not silently treat the thunk as an ordinary value. |
| Catch body returns a thunk value | Do not invent a force at catch entry. The returned thunk passes through the value-arm path with its latent effect and captured wrapper intact, unless a later concrete operation forces it. |
| Pattern/default binding | Transfer the bound value and any latent thunk/continuation facts into the bound slot. Binding alone is not a force; retain latent evidence until a concrete force or invocation site. |

For these cases, the endpoint-plus-observation goal is conditional: if the
value-slot relation represents the concrete thunk and its captured wrapper,
and the exact-spine premise or top-edge premise holds, each concrete step has
an abstract successor containing the concrete endpoint and an observation
covering every request offered on that edge. This follows case-by-case from
the runtime constructors: operation application constructs the effect thunk;
effect force calls request emission; continuation application constructs its
thunk; continuation force invokes the saved resumption and forces a thunk
result. For `Thunk::Expr`, force evaluates its stored body/environment;
`Thunk::Value` returns its saved value; `Thunk::Adapter` recursively forces
then adapts. For a marked continuation, application applies
`markers_for_continuation_call`, and closing that marker frame marks the
returned continuation thunk; forcing the thunk later reactivates those
transformed markers in addition to consulting the saved continuation wrapper.
These are separate evidence carried by the thunk fact, not interchangeable
with the wrapper captured when `k` was created. Callee/argument evaluation is
a preceding sequence of steps, not hidden by the application case.

This conditional local argument still does not construct the source-to-slot
relation, prove captured-wrapper summaries finite and complete, establish
endpoint preservation for every continuation state, or show that effect-row
slots receive every thunk latent row. The current frozen-runtime force-site
inventory is:

| Oracle site (main at `a58eefc3`) | Force / non-force behavior relevant to the transfer |
|---|---|
| `runtime/eval.rs::ExprKind::ForceThunk` | Explicitly force the evaluated value once; if the declared target is not a thunk, force the result too when it is thunk-like. |
| `runtime/flow.rs::apply_value` | A thunk used as callee is forced before applying the resulting value. Applying `EffectOp`/`Continuation` instead creates a latent thunk. |
| `runtime/thunk.rs::adapt_value`, `force_thunk` | Adapting thunk to a non-thunk forces it; `Thunk::Adapter` recursively forces then adapts. Thunk-to-thunk adaptation remains latent. `force_thunk` also evaluates `Thunk::Expr` bodies and returns `Thunk::Value` contents. |
| `runtime/eval.rs::ExprKind::RefSet`, `resolve_ref_set_value` | Force reference and assigned value, invoke `update_effect`, and recursively inspect aggregates; nested thunk-like values encountered during ref-set resolution are forced. |
| `runtime/eval.rs::ExprKind::Case` | Force the scrutinee before pattern matching. |
| `runtime/eval.rs::eval_handler_body` | Force the operation-arm or continuation-arm body's returned value. |
| `runtime/thunk.rs::force_thunk` continuation case | Invoke the saved resumption and recursively force a thunk-valued result. Effect thunks emit requests here. |
| `runtime/eval.rs::eval_catch`, `handle_catch_value` | Do not force a returned thunk; route the `Value` directly through catch value arms. |
| `runtime/bind.rs::bind_record_pat`, `runtime/thunk.rs::continue_value_as_bind` | Evaluate a missing-field default, then bind its returned value without forcing a thunk result. Preserve latent evidence in the bound value. |
| `runtime/eval.rs::eval_block_step` | Let/expression steps pass returned values onward without a general force. |

This inventory is over runtime call sites found by enumerating every direct
`force_thunk` / `force_value_if_thunk` call in the frozen runtime, plus the
recursive ref-set visitor and the marker wrapper around force. It corrects the
earlier mistaken catch-entry force classification. It does not prove that
source-to-slot lowering reaches each site soundly, or that all nested values,
callbacks, and latent rows flow to the right slots. No offer from these cases
may authorize `Drop` until those transfer and global handler-scope proofs
close.

#### `RefSet` as a relational composition (runtime characterization)

The frozen implementation does not make `RefSet` equivalent to a primitive
heap write. In `a58eefc3:crates/mono-runtime/src/runtime/eval.rs`, it evaluates
and forces the reference, evaluates and forces the assigned value, projects
the reference's `update_effect` field, applies it to `Unit`, and passes its
result through `handle_ref_set_result`. That routine resumes the exact
`std.control.var.ref_update.update` request with the assigned value; other
requests are forwarded after recursively resolving their payload, with a
continuation that re-enters the same result handler. At final return it
recursively resolves the returned value and then returns `Unit`.

The helper can be expressed using the same resumable computation, bind, force,
and structural value traversal already used elsewhere. Write `u` for the exact
internal update operation, `v` for the forced assigned value, and `F` for the
result action. The runtime's two result handlers are instances of one
parameterized transformer:

```text
Finish_v^F(Return(x,c)) = Resolve_v(x,c) >>= F

Finish_v^F(Request(h,p,k,c)) =
  if path(h) = [std, control, var, ref_update, update]
    then Finish_v^F(k(v))
  else Resolve_v(p,c) >>= (λ(p',c').
         Request(h,p', λx. Finish_v^F(k(x)), c'))
```

Here `h=(path, guard_ids, carried_guards, handler_boundary)` is the request
header. Forwarding preserves `h` exactly; only the resolved payload and the
continuation wrapper change. `c'` is the live state after resolving the payload,
and resumption continues from that state.

The outer `handle_ref_set_result` uses `F(x)=Return(Unit)`; nested thunk
resolution uses `F(x)=Return(x)`. `Resolve_v` is the ordered structural
traversal from `resolve_ref_set_value`: scalars return unchanged; marked
values resolve the wrapped value and reapply the marker to its eventual
result; tuple/list/record/variant/constructor children are resolved
left-to-right with ordinary state-threaded bind; a thunk-like value is forced
and its `EvalResult` is fed through `Finish_v^{Return}`. Thus a request while
resolving a child keeps the remaining aggregate traversal in its continuation.
The full `RefSet` sequence is:

```text
Run(e_ref) >>= ForceValue >>= (λr.
  Run(e_value) >>= ForceValue >>= (λv.
    Finish_v^{Return(Unit)}(
      ApplyValue(Project(r, "update_effect"), Unit))))
```

This equation is a reconstruction of the frozen runtime helper, not a new
typing rule or an assumption that mutation itself is pure. The exact update
callback's effects and state changes remain in `ApplyValue` and its resumed
continuations. Each non-update request remains observable after payload
resolution and is re-forwarded with re-entry; each update request is resumed
with `v`, and effects in that resumed suffix are handled by the same
transformer. Aggregate traversal adds no independent row rule: its requests
are those of ordinary `Resolve` composition and `Force`.

The local equation supports a conditional endpoint/observation simulation:
if `Run`, `ForceValue`, `ApplyValue`, `Project`, `Resolve`, and the exact
operation identity `u` already have related source/abstract steps, then a case
analysis on the `EvalResult` constructors preserves each request edge, and
structural induction on finite aggregate values preserves traversal order and
the remaining-child continuation. On a thunk, the induction reduces to the
same `Finish` request cases. It must carry `v` as a complete live value root
through every resume and preserve its symbolic family formulas and reference
graph. This conditional proof does not show the source typing meaning of
`update_effect`, that source lowering makes the evaluated operands live roots,
that arbitrary/cyclic aggregate traversal has a finite abstraction, or that
the resulting `Σ#`/effect interface is principal. The frozen runtime observation
is characterization evidence only; any successor rule still has to follow
the independent declarative source semantics and soundness proof. A focused
compiler-referee delta review found no mismatch in exact request-header
preservation, update-path matching, payload resolution, or live-state
continuation threading.

#### Candidate runtime-value coverage for one ghost-tagged mono executable

The concrete runtime audit supports a structural slot relation for one frozen
mono executable `P`, provided expression execution and pattern matching are
ghost-tagged with their static occurrences. Let `MonoSite(P)` be the finite
structural paths through the root and instance expression and pattern trees,
including child, arm, statement, pattern, pattern-default, and payload
positions. A logical tagged evaluation carries the current `MonoSite` when it
enters an expression or pattern match and preserves the creator site when a
closure or thunk stores a cloned body for later re-entry. Erasing
these ghost tags must recover exactly the frozen runtime steps; that erasure
simulation is a proof obligation, not an existing runtime field. It does not
supply source identity across a family of polymorphic specializations. Define
slots from finite products of those sites, `DefId`, `InstanceId`, field names,
and child positions:

```text
Result(e)          expression result
Child(e, i)        aggregate/application child
Field(e, name)     named record field
ListElem(e)        union of all dynamic list elements produced at e
Def(d)             local binding
CaptureProjection(e, d) diagnostic projection of captured local d at e
InstanceValue(i)   runtime instance cache entry
RefValue(e, path)  reference-like nested location rooted at e, with path from
                   a fixed finite structural-path set
Kont(e, arm)       continuation created for catch arm site and arm position
```

All indices come from the finite mono expression/pattern trees. `path` is not
an arbitrary runtime path language: fix a finite set of structural paths per
source closure and widen any deeper or unknown shape to `TopValue`.

Each result slot stores a powerset of whole finite `ValueFact#` tuples. A
tuple contains its shape, callable origin, latent rows, nested child facts,
and auxiliary snapshot together. Child/field/list/capture projection slots
are inclusion indices only; capture and call use immutable references to the
whole interned `ValueFact#` tuples, never a lookup in a site-wide union slot.
When construction has multiple possible child facts, preserve the complete
parent/child tuple alternatives; if the finite relation cannot retain them,
widen the whole parent fact to top. `Pt` is only the callable-origin projection
of this relation; it is not joined independently back with `Aux` or latent rows
to make a call or `Drop` decision. Capture and route evidence must be
relational: a `Snapshot#` tuple contains the complete captured environment as
`DefId -> interned whole-ValueFact# reference` entries, ordered marker transform, saved continuation
control, and handler/scope/mask facts. It must retain captured value facts,
not merely point to `CaptureProjection(e,d)`, because that global projection
may contain values from another dynamic activation. Joining activations unions
complete tuples; it must not independently union their fields and recreate a
Cartesian product. On a closure call, captured `DefId` reads use the value
fact inside the snapshot paired with that closure origin. `CaptureProjection`
is useful for inclusion propagation but never authorizes re-pairing a captured
value with an unrelated snapshot.

To make nested captured values finite, choose a finite structural depth `K`
for `ValueFact#` and `Snapshot#`; beyond `K`, widen the **combined** value,
control, and effect summary to `TopValue`/`TopControl`/`TopKont`/`⊤Eff` before
any route or `Drop` decision. `TopValue` retains `⊤Eff` as a latent bound; it
does not eagerly add that row to a computation until the value is projected,
called, forced, or re-entered. Such later use keeps top immediate/latent rows
and top request/blocker observations at every compatible handler slot, and
emits `TopObs` before any possible request dispatch. The snapshot quotient may
also retain bounded exact stacks. Joining must preserve all tuples within the
quotient and use the full top fallback for unrepresentable or ambiguous
cross-activation relations. Runtime `ContinuationId` and `GuardId` are never
reusable static identities. `ShapeFact` records
scalar/aggregate/callable/thunk/adapter/continuation kind; latent rows remain
tuple fields. Top facts absorb any shape, nested callable, continuation,
boundary, or effect information that the finite local relation cannot
represent.

The relation `CoversValue_P(v, s, A)` is a structural simulation hypothesis:
the runtime value `v` placed at concrete slot `s` is covered by abstract facts
`A` at the corresponding slot. Its constructor clauses are:

| Runtime value class | Required slot coverage |
|---|---|
| scalar (`Int`, `BigInt`, `Float`, `Str`, `Bytes`, `Bool`, `Unit`) | Add its finite scalar shape; it contributes no callable origin. |
| `Tuple`, `Record`, `PolyVariant`, `DataConstructor` | Add the outer shape and retain each tuple/payload position or record-name field as nested whole child facts; also publish `Child`/`Field` inclusion projections. Spreads and duplicate/unknown fields union complete alternatives; unrepresentable fields become `TopValue`. |
| `List` | Retain element facts in the list's whole value tuple and publish `ListElem(e)` as an inclusion projection. An exact statically known index may select its positional child fact; unknown index, dynamic length, or slice uses the element union inside that same parent tuple, and an unknown source shape widens to `TopValue`. |
| `Closure`, `RecursiveClosure` | Add a joint `(body origin, Snapshot#)` fact whose map stores every captured `DefId`'s `ValueFact#`; recursive self insertion flows through `Def(d)` and back to the closure origin at the same finite body site. |
| `PrimitiveOp` | Add its primitive producer origin and retain accumulated partial arguments inside the same `ValueFact#` tuple, with child slots as projections only. Its completion rule must have a proved output-shape summary; otherwise its result is `TopValue`, including callable values extracted from aggregates. |
| `ConstructorFunction` | Add the constructor origin and retain accumulated arguments inside the same `ValueFact#` tuple; saturation packages those values into `DataConstructor` payload slots. |
| `EffectOp` | Add the operation producer/path origin; applying it packages the payload into `Thunk::Effect` with a latent family fact. |
| `Continuation(id)` | Relate to the finite catch-arm `Kont(e,arm)` slot when the source arm is known; include the saved continuation/wrapper and call-result marker transform in `Aux`. If dynamic activation identity or saved control is unresolved, widen to `TopKont`/`TopControl`. |
| `Thunk::Expr`, `Thunk::Value`, `Thunk::Effect`, `Thunk::Continuation`, `Thunk::Adapter` | Preserve thunk kind and latent row, then recursively relate the captured expression environment, returned value, payload, continuation slot, or inner thunk/adaptation. Marker evidence is carried separately in `Aux`; unresolved captured scope widens to top. |
| `FunctionAdapter`, `Marked` | Recursively preserve the wrapped callable target set and nested value slots; append adapter hygiene or runtime marker transformation to `Aux`. If ordered wrappers cannot be represented by the finite quotient, widen route/control evidence to top without deleting callable origins. |

Locals and pattern binds move value-fact references along the exact finite
`DefId` edges; tuple/list/record/variant/constructor projections read the
matching child facts from the parent tuple and may publish them to child,
element, or field projection slots. Record defaults add their expression result as an
alternative for the missing-field branch and include its latent effect even
though binding itself does not force it. Ref-set updates flow through the
reference-shaped slots and the `update_effect` call/result; unmodeled host
values or aggregate shapes seed `TopValue`. Runtime `InstanceId` is already a
finite executable key. Runtime `ContinuationId` and `GuardId` are fresh dynamic
counters, so they may only map to finite source arm/boundary slots when the
saved control/marker relation is covered; otherwise use top rather than
equating dynamic IDs with static sites.

For a fixed `P`, this clause set is finite because all slots are generated
from finite structural paths and the row/origin sets are finite. The clauses
do not yet prove `CoversValue_P` inductive for all runtime steps; in particular,
primitive summaries, arbitrary selection, the mono-to-slot ghost-tag erasure
simulation, escaped closure re-entry, and the finite marker/continuation
quotient remain premises. Nor does this prove a source-level slot map across
specializations: current mono IR retains sparse application/selection
provenance, but not a source-arena `PolyExprId` on every lambda, aggregate,
thunk, pattern, or generated value. `BodySrc(S)` to `MonoSite(P)` transport
therefore needs an explicit provenance map, or else cross-assignment analysis
must use the broad `BodySrc(S)`/`TopValue` fallback. This relation is a
proposed base case for the `γP` source/runtime invariant, not a soundness
theorem or a positive `Drop` certificate.

#### Conditional ghost-tag erasure lemma for closure/thunk re-entry

For one fixed `mono::Program P`, define `decorate(P)` by assigning each root,
instance body, and nested `Expr` occurrence its unique `MonoSite(P)` structural
path. Child paths follow the actual `ExprKind` field/vector position, including
lambda and thunk bodies, pattern defaults, case/catch arms, guards, block
statements, and record/tuple/variant payloads. A tagged closure stores the
original body plus its body site and one correlated capture snapshot; a tagged
`Thunk::Expr` stores the original body plus its body site and capture snapshot.
The tag is ghost state and is erased before every Oracle operation on `Value`.

Write `erase(κ#)` for the Oracle runtime configuration obtained by deleting
all `MonoSite`, `ValueFact#`, and `Snapshot#` metadata from a tagged
configuration. The local lemma is:

```text
κ# --closure/thunk step--> κ'#
    implies
erase(κ#) --Oracle step--> erase(κ'#)
```

for the following finite cases, provided every stored body has the site
assigned by `decorate(P)` and every captured environment snapshot erases to
the exact raw `CapturedEnv`:

| Tagged case | Erasure argument |
|---|---|
| Evaluate a lambda | The tagged closure stores the same `param`, cloned `body`, and raw environment as `eval_expr`; erasing its metadata yields the Oracle `Value::Closure`. |
| Evaluate `MakeThunk` | The tagged `Thunk::Expr` stores the same cloned body and environment as the Oracle constructor; body site and capture summary erase. |
| Read `Local` or `InstanceRef` | Apply the same raw `mark_active_value` operation as Oracle and attach its marker transform to the correlated metadata. Instance evaluation uses the same finite `InstanceId` cache and raw body; cache hits do not create a new body origin. |
| Apply `Closure` or `RecursiveClosure` | The raw parameter binding/body evaluation is unchanged. A recursive call inserts the same self value at `DefId`; the tagged environment adds its paired closure fact and erases to that same updated environment. The stored body site, rather than structural equality of the clone, selects the re-entry slot. |
| Force `Thunk::Expr` | The tagged evaluator evaluates the stored raw body and environment at its saved `MonoSite`; erasing the result yields the same Oracle body evaluation. |
| Construct/copy through `Marked` or `FunctionAdapter` | The raw wrapper/marker/adaptation step remains the Oracle one; metadata follows it as a correlated fact and cannot change marker dispatch. |
| `adapt_value`: thunk to thunk | Oracle creates `Thunk::Adapter` around the same raw inner thunk. The tagged adapter records the same source/target wrapper and its inner correlated fact; erasure yields the Oracle adapter. |
| `adapt_value`: value to thunk | Oracle recursively adapts the raw value and creates `Thunk::Value`. The tagged form stores that same adapted raw value and its correlated fact; erasure yields the Oracle thunk. |
| Force `Thunk::Value` | Oracle returns the saved raw value. The tagged transition returns that same raw value and associated fact, which erases away. |
| Force `Thunk::Adapter` | Oracle recursively forces the inner thunk, then applies the same `adapt_value` to the result. The tagged transition uses the corresponding inner fact and wrapper relation; each recursive force/adaptation is one of these listed cases, and any `continue_with` callback keeps the same raw callback and carries only correlated metadata. |
| `adapt_value`: thunk to non-thunk | Oracle forces the thunk before adapting the result. The tagged path delegates to the listed force cases, then applies the same raw adaptation; nested aggregate adaptation is covered only where it reduces to those same value/adaptation cases. |

Proof for these cases is by inspecting the corresponding constructors and
transfers in frozen `eval_expr`, `apply_closure`, `apply_recursive_closure`,
`force_thunk`, `adapt_value`, and marker wrapping: each raw field and raw
transition is identical after erasure. The `Thunk::Adapter` case is conditional
on the recursive inner force/adaptation using the same relation; it does not
assume that recursion terminates. The result establishes only tag erasure for these
operations, not that the generated `ValueFact#` relation covers every source
step. In particular, it does not prove primitive output summaries, aggregate
projection completeness, the source-to-mono specialization map, continuation
snapshot coverage, the finite wrapper quotient, or the effect-row/offer
coupling. A later control-IR implementation still needs a separate
mono-runtime-to-control-IR simulation; this ghost-tag lemma does not identify
mono runtime values with Control-IR `ExprId`s.

#### Latent-row transport invariant for whole value facts (candidate)

An origin set or family row by itself is insufficient for higher-order effect
soundness: the same family can be offered under different handler snapshots,
and a value can carry a computation that has not run yet. Keep latent effects
inside the correlated whole `ValueFact#` / `Snapshot#` relation. For a concrete
value `v` related to whole fact `F`, `LatentCover(v,F)` means every deferred
call, force, or resume reachable through `v` is paired with its effect upper
row, nested whole-value references, captured environment, ordered wrapper,
and route/scope evidence, or the complete corresponding top fact. This is an
invariant over future eliminations of `v`, not a row charged immediately just
because the value is returned, stored, or copied.

| Value-flow event | Required row/provenance transfer |
|---|---|
| Create or copy a closure | Retain its body-call row and the same correlated capture snapshot. A later call reads captured facts from that snapshot; it does not reconstruct them from site-wide unions. |
| Create `Thunk::Expr` or `Thunk::Value` | Retain the deferred body's or saved value's facts and latent rows. Binding, returning, or storing the thunk does not charge them immediately. |
| Apply an effect operation or continuation | Retain its family or saved-continuation row in the resulting thunk and preserve the creation marker/snapshot. Emit no request or resumed-suffix offer until the concrete force/re-entry event. |
| Wrap with `Marked`, `FunctionAdapter`, or `Thunk::Adapter` | Preserve the entire underlying fact and append the ordered wrapper/boundary transform. If the row or transform cannot be related across the adaptation, widen the entire value/control/effect fact to top. |
| Project, return, copy, bind, or store without forcing | Transfer the selected whole fact, including nested latent rows and snapshots, to the destination. Keep its row latent and emit no offer solely because the value moved. |
| Evaluate an application's callee | Simulate callee evaluation first and charge its actual computation bound/offers before dispatching the resulting value. |
| Adapt argument computation to a value domain | Evaluate an unsuspended argument or force/adapt a suspended one before entering the closure. Include its evaluation/force computation row and offers at the actual argument/adaptation context, then bind the resulting whole value fact. |
| Adapt argument computation to a suspended domain | Preserve an existing thunk or wrap the argument computation without evaluating its body. Retain its row, origin, captured environment, and wrapper/scope snapshot as latent facts. A later force relates that retained snapshot and ordered wrapper transforms to the force-site active handler/receiving context; unknown relation widens to top. |
| Apply `Closure` or `RecursiveClosure` | Account for the function body's evaluation in the application computation bound and preserve the returned value's whole fact. The relation from that bound to source `ret_eff` remains to be proved. Do not force a thunk-valued result unless a concrete force site does so. |
| Unknown or assignment-dependent accepted domain/adaptation | Join value-domain and suspended-domain transfers for all admissible adaptations, keeping immediate and latent routes distinct. If their correlation cannot be retained, widen to the whole top fact; do not choose an adaptation from row denotation or a frozen Oracle syntax branch. |
| Force `Thunk::Value` | Return the saved whole value fact; emit no request merely for forcing this variant. If the returned value is itself thunk-like and the concrete force site forces again, account for that separate force. |
| Force `Thunk::Expr`, `Thunk::Effect`, `Thunk::Continuation`, or `Thunk::Adapter` | Evaluate the saved body, emit the saved operation request, resume the saved continuation and recursively force a thunk-valued resume result, or recursively force/adapt the inner thunk, respectively. Transfer the matching latent row and captured wrapper facts; emit request observations only on request-producing steps. |
| Unknown call/force/resume target or lost capture relation | Use `⊤Eff`, `TopKont`, and `TopObs` at every compatible handler slot, and preserve the top summary through the returned value. |
| Instantiate a local binder | Apply the use's effect-binder substitution consistently through the whole value and evidence payload, while freshening local hygiene binders independently. Unknown ownership/mapping takes the top fallback. |

Conditional invariant: if each concrete event above is represented by these
transfers, then packaging, returning, copying, and escaping preserve
`LatentCover`; a later call/force/resume exposes the retained bound and route
facts rather than silently consuming them. The top alternative is absorbing,
so loss of a wrapper, latent row, target, or correlation cannot authorize
`Drop`. This uses no continuation-use count and does not claim exact trace
support: an arm can retain the whole pre-handler bound on raw `k` even when
its concrete suffix does nothing. Exact finite traces remain the soundness
reference, and principality remains relative to this compositional
abstraction.

This invariant is not yet established by the listed runtime-local erasure
lemmas. The value-domain and suspended-domain rows describe an already
determined argument boundary adaptation; they do not select that adaptation
from the argument row or claim that every call has one of these modes. The
candidate still does not establish which source constraints determine the
callee's accepted domain, where an adapter is introduced, or how those source
steps correspond to the specializer's materialized shape. In particular,
source `arg_eff` / `ret_eff` constraints do not yet prove whether an
effectful input is forced before a closure body or preserved as a thunk; a
source-to-elaboration boundary relation must prove that distinction. The
ordinary application bridge, adapter row transport, use-site substitution,
and coupling of each latent contribution to offers versus matched raw
continuations remain open. See
`notes/progress/2026-09-30-intrusion-oracle-latent-effects.md`, “Candidate
mode-indexed application obligation”; that Oracle characterization does not
select this successor rule.

#### Restricted source-annotation to domain characterization

The ordinary-application bridge can be narrowed for an explicitly annotated
lambda parameter, without claiming the general case. In the frozen Oracle,
`connect_lambda_pattern_annotation` gives an unannotated parameter the
`never_neg()` argument-effect endpoint and no effect stack. An ordinary value
annotation such as `int` follows the non-effectful branch of
`lambda_param_effect_slot` and `connect_parameter_computation_detailed`; it
also keeps the pure argument-effect endpoint and has no effect-stack
connection. An `AnnType::Effectful` parameter instead starts with a fresh
effect variable;
`connect_parameter_computation_detailed` connects it to the annotation row
and returns an effect-stack connection. For the wildcard row in the focused
`[_] int` fixture, that connection uses the full effect endpoint. The lambda
predicate stores that endpoint as `arg_eff`, and `specialize2::lambda_type`
binds the parameter through `runtime_shape(arg_effect, arg)`.

The existing exact characterization pair is:

```yu
my strict(x: int) = 1
my defer(x: [_] int) = 1
```

The finalized predicates in the disposable `a58eefc3` probe had
`strict.arg_eff = Bot` and `defer.arg_eff = Top`; runtime materialization
therefore produced a plain `int` domain for the first and
`Thunk(Any,int)` for the second. The focused specialization probe completed
both cases. Mono output placed a `ForceThunk` on the plain-value path and a
`MakeThunk` around the effectful body on the suspended path. The programs were
not executed. Runtime `adapt_value` forces
thunk-to-value adaptation and preserves thunk-to-thunk adaptation. The prior
Oracle note records the exact probe and its limits; this paragraph links its
source-lowering endpoints and runtime-domain shape. The source locators are
frozen `a58eefc3`: `crates/infer/src/lowering/expr/lambda.rs:1252-1264,1266-1326,1344-1354`,
`crates/infer/src/annotation/constraints.rs:251-280,546-590`,
`crates/specialize/src/specialize2/task_solver.rs:605-620`, and
`crates/specialize/src/types/mod.rs:401-426`. The focused application path is
`crates/specialize/src/solve/expr_solver.rs:354-388`; runtime adaptation is
`crates/mono-runtime/src/runtime/thunk.rs:4-45`. No Oracle inference-stage
scheme formatting is required by the successor.

A candidate declarative distinction suggested by this witness is to make the
accepted domain explicit in the source judgment: `Value(A)` for an ordinary
parameter and `Susp(U,A)` for an effectful parameter with latent allowance
`U`. Application then adapts the argument to that domain using the four cases
above; domain selection does not inspect the actual argument row. This gives
an independent semantic vocabulary for the witness, but it is not yet a
selected successor rule or a theorem. Making these constructors stable source
domains would be a new semantic decision: it requires Function subtyping,
generalization, instantiation, and adapter coherence rules. `U` means only a
latent effect allowance under a proved subeffect constraint; the fixture's
Oracle `Top` neither defines `U` generally nor grants handler visibility. The
witness covers explicit plain and wildcard-effect parameter annotations only.
It does not establish domain
transport through inferred/unannotated higher-order values, bounds that join
the two domains, independent use instantiation, function adapters, or nested
effect rows. The next proof must show how the candidate domain constructor is
preserved by subtyping and generalization, or retain both domains with a
conservative top transfer when it cannot be determined.

#### Conditional trace derivation for force versus ignore

The direct source judgment suggested by the explicit-domain candidate can be
checked without Oracle weights or continuation-use counts. Let an effectful
argument be a suspension of exact computation `C_out`, where
`C_out = Request(out.read, (), λn.Return(n))`, with family support
`{out}`. Let `force(Susp(C)) = C`. Define closure application after boundary
adaptation: a `Value(A)` formal forces a suspended argument before evaluating
the closure body; a `Susp(U,A)` formal receives the suspension unchanged,
subject to its latent allowance. The concrete suspended call below requires
`{out} ⊆ U`. For an open function formal, the reusable contract must establish
that every admissible actual suspension, including nested force/adaptation
effects, has latent row bounded by `U`. Assume a closed pure callee, no
handlers, adapters, recursion, or other effects, and an operation continuation
that returns its result without a suffix request. This is a candidate source
rule for the direct fragment, not an adopted Yulang semantics.

For two ignoring bodies and one body that forces its argument, the trace
calculations are:

| Function domain and body | Argument boundary | Exact call trace support | Exact body trace support / fixed-call `ret_eff` bound |
|---|---|---:|---:|
| `Value(int)`, body returns `1` | Force `C_out` before closure entry | `{out}` | `∅` |
| `Susp(U,int)`, body returns `1` without using its parameter | Retain `Susp(C_out)` | `∅` | `∅` |
| `Susp(U,int)`, body forces its parameter before returning | Force `C_out` in the body | `{out}` | `{out}` |

The first row's request belongs to the application boundary computation, not
the function body's `ret_eff`. In the second row, the argument's `{out}` is a
latent fact; returning or dropping the unused suspension does not emit a
request and does not add `{out}` to `ret_eff`. In the third row, the fixed
trace proves only that this body's bound contains `{out}`. Charging all of
`U` to the reusable function `ret_eff` is a separate conservative transfer
proposal: it is sound only if `U` bounds every admissible suspended input and
the force path has no local handler that soundly removes part of that bound.
No leastness or necessity of `U` follows from this single trace. The three
trace results are direct consequences of the candidate force/adapt rules and
the free-tree trace semantics in
`2026-09-30-intrusion-shallow-handler-trace-calculus.md`; they need no linear
or affine typing because the cases concern whether an ordinary delayed value
is forced, not how many times a continuation is resumed.

This derivation establishes only the effect timing of the proposed direct
application rules. It does not prove that a source annotation means the
corresponding stable domain, that ordinary inference retains the `Susp`
latent row through higher-order use, or that the abstraction can distinguish
ignore from force while remaining principal. It also omits handler routing:
if a shallow handler surrounds the application, a strict request is offered
at the argument adaptation point; a deferred request is offered only if and
where a later force executes `C_out`. Proving which activation is eligible at
that force requires the separate route/scope simulation. Exact traces remain
the soundness reference; successor rows may conservatively retain more than
these exact supports.

#### Candidate transfer for an already selected value/suspension boundary

To make the preceding inventory compositional, represent an evaluated
argument fact as either `Value(F)` or `Susp(E_latent,F)`, together with any
effect `E_now` already produced while evaluating the argument expression.
These are semantic categories for the candidate judgment, not source syntax
and not an inference rule for choosing the callee's accepted domain. A
suspension retains the whole value fact `F`, including captures and boundary
evidence.

For a fixed boundary adaptation, use these transfers:

| Source fact | Accepted callee domain | Immediate effect added here | Returned fact |
|---|---|---|---|
| `Value(F)` | value `A` | effects from evaluating the argument (`E_now`) and any immediate value adaptation | adapted `Value(F')` |
| `Susp(E_latent,F)` | value `A` | `E_now ∨ E_latent ∨ E_adapt-now` because the suspended computation must run before closure entry | adapted `Value(F')` |
| `Value(F)` | suspended `Susp(A)` | `E_now ∨ E_adapt-now`; wrapping the already computed value adds no latent request | `Susp(∅, F')` |
| `Susp(E_latent,F)` | suspended `Susp(A)` | `E_now`; retain latent work and defer any adaptation that the suspended boundary requires until force | `Susp(E_latent ∨ E_adapt-latent, F')` |

`E_adapt-now` and `E_adapt-latent` are themselves computed by the same rule
for nested boundaries, not erased because an adapter is administrative.
For a suspended target with an explicit latent-effect allowance `U`, the
boundary is admissible only when the produced latent row is bounded by `U`;
otherwise the typing constraint rejects that adaptation (or an unknown
relation widens to top and cannot certify acceptance).
When calling through a function adapter, compose the stages in order:
adapt the external argument to the wrapped function's input, run that
function, then adapt its result to the external result. Join their immediate
rows in `D_eff`, while preserving the ordered wrapper and route evidence in
the correlated whole fact. An unknown source/target relation yields the
whole top fact and `⊤Eff`; it cannot justify `Drop`.

The local preservation claim is conditional: if the source judgment defines
`Value` and `Susp` as immediate values and explicit delayed computations, and
each boundary operation has the stated force/wrap semantics, then these four
cases neither omit a forcing effect nor charge a retained latent effect
before its force. This does not prove that source `arg_eff` / `ret_eff`
constraints determine the boundary, that all function boundaries have these
two forms, or that handlers observe each stage under the right activation.
The frozen `adapt_value` force inventory appears above under “Conditional
thunk-step simulation cases”; its conditional tagged-erasure cases appear in
the preceding “Candidate runtime-value coverage for one ghost-tagged mono
executable” subsection. `apply_adapter`'s argument-adapt / call / result-adapt
order is characterized by frozen `crates/mono-runtime/src/runtime/flow.rs`
and the nested adapter trace recorded earlier in this candidate. These are
separate characterization evidence, not the semantic authority for this
transfer. The latent-effects note records mode and generated-shape
characterization, not these adapter details. Principal inference still
requires that these transfer inequalities be integrated into the fixed-`Drop`
effect operator and that derivations match its least solutions.

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

##### Nested forwarded-wrapper expansion (source-calculus lemma)

This witness gives a direct expansion of the two wrappers, without a bounded
machine or weight rule. Assume `I` forwards `u`, handles `p`, and its `p` arm
performs `g`; assume `H` forwards both `u` and `p`, handles `g`, and the outer
context resumes `u` with a value `r`. Eligibility is parameterized: `I` is
eligible for `p`, and `H` for `g`.

```text
I(C0) = Request(u, (), λr. I(k0(r)))
H(I(C0)) = Request(u, (), λr. H(I(k0(r))))
k0(r) = Request(p, (), λs. Return(0))
I(k0(r)) = evaluate_I_p_arm((), λs. Return(0))
```

After the outer context resumes the forwarded `u`, the continuation therefore
executes `H(I(k0(r)))`; the `p` arm emits `g` while `I` is inactive, and the
still-installed `H` sees and handles `g`. The offered sequence includes `u`
at `I`, `u` at `H`, then `p` at the re-entered `I`, then `g` at `H`. The
continuation is not `H(k0(r))`: that omission loses the `p` arm and its `g`
offer. A matched raw continuation would differ: matching `u` at `H` would run
its arm with the raw suffix and would not reapply `H`. This expansion follows
by substituting the shallow `Request` clause twice and distinguishes wrapper
composition from raw resumption. It proves no grant/scope judgment, finite
abstract transfer, top-fallback completeness, or source-to-runtime
correspondence.

A focused compiler-referee delta review found no issue in this definitional
expansion. It confirmed the `I:u → H:u → I:p → H:g` offer order and the raw
`H`-matched contrast, under the stated eligibility assumptions. This closes
only the source-calculus wrapper trace; finite transfer, row-to-offer coupling,
and runtime correspondence remain unproved.

##### Finite nested-forwarding equation

The same calculation generalizes to a finite nesting of shallow handlers.
Write `H_j ∘ ... ∘ H_1` for nested application with `H_1` innermost. If every
`H_i` forwards the request `q`, repeated expansion of the forwarding clause
gives the equation below. An empty prefix or suffix denotes the identity
transformer.

```text
(H_n ∘ ... ∘ H_1)(Request(q,k))
    = Request(q, λx. (H_n ∘ ... ∘ H_1)(k(x)))
```

If instead the first matching-and-eligible handler is `H_j`, assume all inner
`H_i` for `i < j` forward `q`. Their wrappers compose into the continuation
received by `H_j`; the handler result remains under every outer handler:

```text
H_n(... H_{j+1}(H_j(H_{j-1}(... H_1(Request(q,k)) ...))) ...)
  = H_n(... H_{j+1}(
      arm_j(payload, λx. (H_{j-1} ∘ ... ∘ H_1)(k(x)))
    ) ...)
```

The resumed suffix therefore retains the inner forwarded wrappers, but not
`H_j` itself. The outer handlers surround `arm_j` execution, including any
raw-continuation invocation made there; the raw continuation does not capture
those outer handlers if the arm exports it and it is called later. Induction on
the number of wrappers proves the first equation; expanding the inner prefix,
applying the matching clause once at `H_j`, then retaining the outer context
proves the second.
This is a source-calculus equation under explicit forwarding/eligibility
premises. It does not give the bounded machine a way to represent these
wrappers, prove route summaries complete, or track handler visibility; those
remain separate obligations. Repeated continuation invocation clones this
same suffix and adds no usage count.

##### Ordered wrapper transfer for the bounded request-tree fragment

For one request step, represent an exact pending wrapper spine as an
inner-to-outer list of activation references:

```text
W = [h₁,...,hₙ]   // denotes Hₙ(...H₁(C)...)
```

The references are dynamic identities tied to the live/captured scope snapshot,
not static handler sites. At a request `Request(q,k)`, the transfer scans `W`
from `h₁` outward and emits the offer observation for each `hᵢ` before testing
whether that activation forwards or matches:

- If every `hᵢ` forwards, return `Request(q, λx. W(k(x)))`; the immutable
  wrapper spine is retained in the continuation slot and cloned on each
  resume.
- If the first matching-and-eligible activation is `hⱼ`, split
  `W = I · [hⱼ] · O`. Run its arm under outer spine `O`, passing raw
  continuation `λx. I(k(x))`. The current `hⱼ` is absent from that continuation;
  inner forwarded wrappers remain, and outer handlers remain around arm
  execution.
- If a reference is lost, a join merges distinct dynamic identities, or the
  spine exceeds the represented bound, widen the entire ambiguous request step
  to `TopControl`/`UnknownKont`: current offers, possible matching arms and
  their effects, and every resulting continuation/value receive top
  observations and effects under the `UnknownKont` obligations above. Do not
  reconstruct identity from source-site or stack-position equality, and do not
  widen only the future continuation while leaving the current branch precise.

On the fragment with an exact `W` of length at most the bound and no identity
merge, this transfer is a restatement of the finite-nesting equation: scanning
advances precisely over the forwarding prefix, and the first match performs
the same prefix/handler/suffix split. It therefore simulates that one concrete
request-transformer result and emits the same handler offers, assuming
`Eligible` and scope evidence agree. This is a bounded-fragment transfer
lemma, not a proof that
the proposed finite quotient can retain exact references across helper calls,
closure escape/re-entry, or scheme instantiation. The conservative widening
also still needs its full concretization proof.

For observations, record an offer to `H_i` before testing its coverage or
eligibility. Thus an all-forwarded `q` is offered in inner-to-outer order
`H_1,...,H_n`. If the first matching-and-eligible handler is `H_j`, the
original `q` is offered through `H_j` and not to outer `H_{j+1},...,H_n`;
requests emitted by `arm_j` are distinct observations under those still-active
outer handlers. If `q` is forwarded by all wrappers and an outer context
resumes it, the suffix re-enters the same ordered wrapper composition. Each
request in that suffix is offered through its forwarding prefix up to its own
first matching-and-eligible handler; requests emitted by those arms are
observed separately. This follows from the same equations and keeps handler
offers distinct from whole-computation family support and arm effects.

A focused compiler-referee delta review confirmed the offer-before-branch
order, inner-to-outer forwarding, cutoff at the first match, and separate arm
observations. It found one ambiguity about repeated suffix offers; the wording
now scopes the cutoff to each request in the suffix.

##### Handler-relative raw-route corollary

Let `P ≠ Q` and
`C = Request(P.ping, (), λ_. Request(Q.choose, (), λ_. Return(v)))`. Let inner
`I` handle `P.ping` by invoking raw `k`, and let outer `H` handle `Q.choose`.
Then:

```text
I(C) = k(()) = Request(Q.choose, (), λ_. Return(v))
H(I(C)) = H(Request(Q.choose, (), λ_. Return(v)))
```

So `Q.choose` is raw-only relative to `I` (it is not re-offered to `I`) but
is an ordinary offer to outer `H`, which remains around `I`'s operation-arm
execution. The displayed equation assumes `I`'s arm is exactly the pure direct
resume `arm_I((),k)=k(())`; it makes no claim about arm effects or multiple
resumes. If instead the arm is pure and ignores `k`, the `Q` request in `C`'s
suffix is never reached, so that suffix contributes no `Q` offer to `H`.
Therefore route labels must be handler-relative: a contribution must not carry
one global `RawOnly` tag that suppresses a different outer handler's offer.
This follows directly from shallow-transformer composition and introduces no
continuation-use count or exact-inference requirement.

This is a direct two-handler trace case only; source/abstract transfer and
effect-slot coupling remain open.

An initial compiler-referee review found that the witness did not constrain
the matching arm's own effects. The example was narrowed to an exactly pure
direct-resume arm, and the non-resuming statement to the suffix through `k`.
A fresh compiler-referee delta review closed that finding and confirmed the
handler-relative route result. It did not review or establish abstract
transfer or effect-slot coupling.

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
`κ = (D, L, σ, Env, ctl)`: `D` is the ordered word of live dynamic delimiter
instances, `L` is ordered request-boundary lineage, `σ` is the live source
store/state, `Env` contains lexical roots and references reachable from locals,
exports, imports, closures, thunks, and captured continuations, and `ctl` is
the current return/request/arm/call/force/resume control point, evaluated
operand values, and pending wrappers. Continuation values denote the source
`k_offer` closures, including
their already-composed handler transformers; they are not reduced to raw stack
slices or to a snapshot of `σ`. For this candidate, factor `σ` into its live
heap and any other mutable machine-state coordinates; `UnknownStore` covers
untracked heap cells, while `UnknownState` covers untracked non-heap state.

An abstract state `A` contains finite sets of projected stack and lineage
facts, a finite set of abstract control facts, a finite map from static
value/allocation slots to sets of value facts, an abstract live-state `Σ#`, a
map from static handler slots to offered `ReqFact` plus scope relations, and
effect bounds for each static effect slot. A reference value fact carries a
finite points-to set of abstract cell slots. `Σ#` maps each finite cell slot
to possible stored value facts, with `UnknownCell`/`UnknownStore` for targets
not represented precisely and `UnknownState` for other live state not
represented precisely. A strong update is allowed
only for a proven singleton concrete cell; otherwise the abstract write is a
weak update that retains every old and new value possibility. If pointer
identity or mutable state is lost, branch/read behavior widens to every
possible result, and any behavior that cannot be bounded that way takes the
existing `TopControl`/`TopKont`/`⊤Eff` fallback. A control fact names a control
slot or `UnknownControl`, plus any pending continuation kind and wrapper
references. `TopControl` denotes all control slots and pending wrappers and
necessarily carries `TopKont`, `⊤Eff`, and top request observations at every
possible handler destination. A value fact contains its value kind, latent row
(possibly `⊤Eff`), and any captured continuation summary or live-cell
references.
Define `κ ∈ γ(A)` when all of the following hold:

1. `αK(D)` and the bounded projection of `L` occur in the corresponding
   abstract stack/lineage alternatives.
2. Every concrete environment value maps to a static value slot whose fact
   covers its kind, latent effects, captured scope/continuation evidence, and
   reference targets.
3. Every concrete cell reachable from these roots maps to an abstract cell
   slot in `Σ#`, and its current contents are covered by that slot's possible
   stored value facts. Every alias of a concrete cell remains represented by
   the same abstract target or by a may-alias set containing it. If a target
   is lost, `UnknownStore` covers it and all reads or control decisions
   depending on it use the unknown/top transfer.
4. Every other concrete mutable machine-state component is related to its
   `Σ#` abstraction or represented by `UnknownState`; transitions reading or
   branching on it then use the unknown/top transfer.
5. Every concrete request offered to a dynamic handler maps to that handler's
   static slot (or `UnknownHandler`) and to a fact whose family, operation,
   origin, and ordered lineage cover the concrete request, and whose
   `γscope` for each corresponding boundary occurrence contains the concrete
   relation. Every independently active eligibility mask is represented in
   `may_blockers` or by `UnknownMask`; this includes non-boundary provider
   guards. Dynamic boundary instances at one site keep distinct bounded
   occurrence positions; if a projection merges them, the union must contain
   every concrete class and include `UnknownMask` where identity is lost.
6. Every concrete immediate and latent effect is included in its abstract row.
7. The current `ctl` and all pending wrappers/continuations map to an abstract
   control fact, and every value held by that control point (including
   evaluated write operands) maps through the same value/reference and heap
   clauses above. Unknown control identity maps to `UnknownControl`/`TopControl`;
   pending lost wrapper identity maps to `UnknownRef` with top control. Any
   `TopControl` fact carries the top effect/provenance/offer summary above; it
   cannot exist as an untainted control-only marker.
8. For every family in a scrutinee effect bound, its contribution is
   classified by route: a current or forwarded route to a handler is covered
   by an offer fact at every possibly receiving slot; a route confined to a
   matched raw continuation is preserved in that continuation's latent effect
   and the arm/value slot that invokes or exports it; an unresolved or mixed
   route retains all possibilities or widens to unknown. For `⊤Eff`, all
   effect, continuation, offer, and compatible interface destinations are top.

The store clause is a liveness relation, not a snapshot relation. A saved
continuation resumes against the current concrete `σ`; its abstract transfer
reads/writes the same `Σ#` cell slots. Repeated resumes therefore start from
the abstract state produced by the preceding arm/continuation path and join
their possible resulting stores. They do not restore the store values present
when the continuation was captured. Static allocation-site abstraction and
weak updates are finite for a fixed source, but their monotonicity and
simulation are still obligations: `read#`, `write#`, alias/equality tests,
closure capture, and resume must each preserve the stated `γ` relation. In
particular, the candidate has not established that finite site abstraction
preserves enough correlation for useful (or principal) handler subtraction;
top widening is sound only when its value, effect, and request consequences
are propagated together.

##### Conditional heap read/weak-write preservation lemma

The heap part of `γ` yields a small local preservation result, without yet
proving source-level transfer adequacy. Let `addr#` map each concrete live
address to exactly one abstract cell slot; this is a many-to-one allocation
site map, and untracked addresses map to `UnknownCell`. Let `Pts#(r)` be the
abstract points-to set for concrete reference `r`. Let `AbsVal(v)` be the complete abstract value facts covering
`v`, including any captured continuation/reference facts and the symbolic
typed-family predicate plus incidence on which that value depends. Require
`H ∼ H#` to mean: every concrete reachable cell `a` has every current
content `v ∈ H(a)` covered by a complete value fact in `H#(addr#(a))`, and
for every concrete reference edge `r → a`, `addr#(a) ∈ Pts#(r)`. The
relation covers the transitive heap reachable from every live root, including
values currently held by `ctl` as evaluated operands; thus a write operand's
referent graph is covered before the write step. These conditions share the
same canonical abstract cell slot, so reference reachability cannot point to
a slot unrelated to the one that covers the cell's contents. These are
conjunctive facts, not independently marginalized row/type/store projections.

For a concrete read through `r` whose target is `a`, define `read#(H#,Pts#(r))`
as the union of value facts at all possible target slots. Since
`addr#(a) ∈ Pts#(r)`, the slot that covers the concrete cell contents is among
the read targets. If any target is `UnknownCell` or
`UnknownStore`, include `UnknownValue` and its top continuation/effect/request
summary. Then `H ∼ H#` implies the concrete read result is covered by
`read#` directly by that shared slot. Thus the read result remains related
before any subsequent control branch; if that branch depends on top/unknown
data, the top transfer must emit `TopObs` before branching as above.

For a concrete write through `r` that updates `a`, with the evaluated value
`v` included among the live roots before the write, define a weak abstract
write by adjoining `AbsVal(v)` to every possible target slot in `Pts#(r)` and
retaining all old facts. The canonical `addr#(a)` slot is among those targets,
so the updated cell is covered by `AbsVal(v)` there. Every unchanged concrete
cell remains covered by its old fact. If two concrete cells share one abstract
slot, retaining old facts is necessary for the non-updated cell and only adds
a sound possibility for the updated one. Since the transitive referents of
`v` were already covered through the live operand root, adding the reference
edge from `a` introduces no uncovered cell. Therefore if `H ∼ H#`, then
`H[a ↦ v] ∼ write#(H#,Pts#(r),AbsVal(v))`. A strong overwrite is sound only
if the abstract target denotes exactly one concrete cell in every state
represented by `H#` and the write target is definite; a singleton points-to
set by itself is insufficient when allocation sites merge multiple cells.

This proof relies on adjoining complete value facts. Dropping a symbolic
family formula or its view incidence while weakly joining heap contents would
not preserve `H ∼ H#`, even if the projected runtime values matched. The
lemma says nothing about whether source read/write operations are typed,
whether reference identity tests have enough must-alias information, or
whether a returned value/effect bound is principal. It only supplies the
heap-coordinate step needed by a later full-state simulation.

#### RefSet operands and the source state they update

A focused compiler-referee audit establishes the frozen control-flow fact but
also locates the missing abstraction link. In `a58eefc3`, `RefSet` retains the
forced reference while evaluating and forcing the assigned value through
`continue_with`; if either phase yields a request, `continue_with_rc` puts the
remaining computation in that request's resume closure. `handle_ref_set_result`
then retains the assigned value while resolving callback results, forwarding
requests, and resuming them. The runtime's continuation table stores these
resumptions, and forcing a continuation invokes it with the current mutable
`Runtime`. Thus an environment-only root relation is insufficient: an assigned
value may point to a cell reachable only through a suspended continuation.
The candidate `ctl` relation intends to cover evaluated operands and pending
continuations, but the current `γ` definition does not yet extract and relate
all values captured by pending or stored continuation closures. The local
heap lemma remains valid under its explicit live-root premise; this audit does
not discharge that premise.

There is a second boundary: the frozen runtime has no primitive heap update
for `RefSet`. `lib/std/control/var.yu` defines the standard reference protocol
through the `ref_update` effect and implements mutable state in `var.run`'s
`get`/`set` handler. Therefore `H[a ↦ v]` in the conditional heap lemma is an
abstract state step, not a literal Oracle transition at `RefSet`. The
source-level meaning is the relational composition already used in the
`RefSet` characterization—operand evaluation, force, callback application,
and ordinary typed request/handler transitions. Any cell abstraction must
prove a bridge from that effect-owned state and its aliases to abstract cells;
it cannot assume the bridge from the runtime helper name.

The next proof target is a general live-root relation over the source
configuration: current environments and state, control-held values, pending
evaluation continuations, stored resumptions, and their transitively captured
references/formulas. Prove its preservation across ordinary bind, force,
forwarding, handler entry, and repeated resumption against the current state;
then derive the RefSet operand cases by composition. Separately prove whether
the standard `var.run` effect protocol admits the selected abstract cell view.
This keeps captured roots and mutable semantics inside the one computation
relation rather than introducing a RefSet-only semantic construct. Until those
links are proved, neither the local heap lemma nor frozen-runtime
characterization establishes source adequacy.

##### `var.run` as one instance of the generic handler relation

The frozen source `lib/std/control/var.yu` provides a direct handler instance,
not evidence for a primitive cell rule. Its arms are `get(),k -> run s:k s`
and `set s',k -> run s':k()`. Let `H_s` be the generic candidate shallow
handler relation instantiated with those operation clauses; let `c` denote the
separately threaded live machine state, and let a saved continuation accept
both its resume value and the state present when it is invoked. The clauses
derive:

```text
H_s(Return(x,c))         = Return(x,c)
H_s(Get((),k,c))         = H_s(k(s,c))
H_s(Set(s',k,c))         = H_{s'}(k(Unit,c))
H_s(Request(q,p,k,c))    = Request(q,p, λr. H_s(k(r,c_live)))
```

The last equation applies to requests not selected by this activation; the
source handler's ordered eligibility and unwind/re-entry semantics still
govern it. It is the ordinary `Step_H` forwarding clause, not a new `var`
rule. The `get`/`set` equations follow by substituting the source arm bodies
into the generic matched-arm clause, whose continuation is raw relative to
this activation. Any typed-family predicate and its incidence remain attached
to the same complete relation through these calls; the equations act on that
relation, not on a materialized may-row.

The two states must not be conflated. `s` is the value parameter of one
recursive `run` activation. A saved continuation resumed more than once may
re-enter that same captured `s`; a `set` arm creates a recursive activation
with `s'`. By contrast, `c_live` is the current machine state and must flow
from one resume to the next, including mutations made by a previous resume.
Treating `s` as a shared heap cell or restoring `c_live` from a continuation
snapshot would change the source behavior. `var_ref` constructs methods that
issue `get`/`set` operations, so an escaped reference's later dynamic handler
and alias identity cannot be inferred from the fact that the closure was
created during a particular `run` activation.

A focused architect review confirms this conditional derivation from the
frozen source clauses and the generic shallow rule. It also rejects identifying
`s` with an abstract heap cell without a separate ownership/alias theorem.
Unproved premises remain source catch shallowness, operation eligibility and
ordering, continuation capture/re-entry, repeated-resume simulation, and
whether escaping `var_ref` closures address the same state after dynamic
re-entry. The source file is absent at current branch `19f6eba7a`; it was read
from frozen Oracle revision `a58eefc3`, so this is characterization and a
candidate corollary, not source-typing authority.

#### One live capture graph for values, stores, and resumptions

The root obligation can be stated without a `RefSet`-specific semantic rule.
For a source configuration `κ`, let `G(κ)=(N,E,R)` be its reachable object
graph. Nodes are values, mutable cells/state locations, continuation frames or
saved resumptions, and active handler-state instances. Edges are source-defined
containment/capture, reference, current-cell-content, continuation-resume, and
handler-state ownership links. A continuation node also carries its ordered
wrapper composition, the distinction between raw and forwarded resumption,
dynamic activation-identity relationships, boundary lineage, and state needed
to decide eligibility and offers. Activation labels themselves are only
indices; the relation is modulo consistent renaming and observes their
identity/sharing and order. These are continuation semantics, not a
route-certificate ledger. `R` contains the current environment and
control-held values, externally retained roots, and active handler state.
Define `Live(κ)` as the least set containing `R` and closed under `E`. A
continuation is represented by its source evaluation context and captured
environment, not by an opaque host closure; invoking a saved continuation
re-enters it with the current state `σ`, never a state snapshot captured at
creation time.

A finite abstract configuration covers `κ` when there is a node map from every
node in `Live(κ)` to an abstract value/cell/control/handler slot such that:
(i) every root maps to a covered abstract root; (ii) every labeled edge maps to
an abstract edge of the same source meaning; and (iii) each mapped node retains
its complete value, effect, and symbolic typed-family facts with their
incidence. This is one graph-homomorphism condition over the whole live data
configuration, rather than separate reachability tests for environment, heap,
or captured values. By itself it does not preserve continuation behavior:
there must also be an ordered control-simulation relation between source and
abstract continuation nodes. It preserves the wrapper spine, raw-versus-
forwarded status, activation identity/lineage, eligibility, and every request
offer made before or after resume. Abstract slots may merge concrete nodes
only when their joined facts, edges, and continuation denotations still
satisfy both relations. If an activation merge loses that distinction, the
abstract transfer must widen to all compatible offers and cannot subtract a
request on that evidence.

The preservation proof has one reusable shape. For each source transition,
show that new roots either were already reachable or are produced with a
covered value fact; show each new capture/reference/store/handler edge is
present in the abstract transition; then induction on edge-path length gives
coverage of every node reachable in the successor. A source transition that
actually updates a cell is covered because the assigned value node and all
nodes reachable from it were live before the write, and the new cell-content
edge is simulated. `RefSet` only qualifies once its effect-handler state has
been related to such a cell update. Capturing a continuation is covered because
its evaluation context, environment values, ordered wrappers, activation
state, and lineage become outgoing capture edges before the continuation can
escape. Forwarding and multi-shot resumption preserve both these edges and
their order; resumption reads the current abstract `Σ#`, and join records the
stores from all resumed paths. For example, if `I` handles `p` by emitting
`g` while `H` handles `g`, and both forward `u`, resuming forwarded `u` runs
the composed continuation `H(I(k(r)))`: it offers `p` to `I` and then `g` to
`H`. A graph that retains both handler nodes but loses their order or treats
the resumption as raw can change the residual. The control-simulation premise
rules this out. These are consequences of the same relation; they do not
create per-site `Demand` or route obligations.

##### Conditional ordered-forwarding lemma

This ordering consequence follows directly from the candidate shallow
forwarding clause. Let `H₁,…,Hₙ` be nested activations from inner to outer.
For one request that is forwarded at each activation, define `K₀(x)=k(x)`
and `Kᵢ(x)=Hᵢ(Kᵢ₋₁(x))`. Then after all `n` forwards the saved continuation is
`Kₙ`, so resumption executes

```text
Hₙ(Hₙ₋₁(…H₁(k(x))…))
```

Proof is induction on `i`: forwarding through `Hᵢ` replaces the request's
resume with `λx.Hᵢ(Kᵢ₋₁(x))`, which is exactly `Kᵢ`. The order is
noncommutative, and each outer handler acts on every observation of the
preceding inner relation under the live state at that yield. An intermediate
request can be handled before the inner relation returns; any state update
remains live for its next resumption. If `Hⱼ` selects the request instead of
forwarding it,
its arm receives `Kⱼ₋₁` as the continuation raw relative to `Hⱼ`; the current
handler is absent from that continuation, while outer handlers remain around
the arm computation. Thus an inner handler's arm effect can be observed by an
outer handler without re-entering the inner handler.

This proves the wrapper-order fact for the candidate handler relation, not the
finite abstract simulation. The latter must preserve the ordered sequence and
raw/forwarded distinction modulo renaming of activation labels. If abstraction
merges two sequences with different composed denotations, it must widen the
offers soundly and cannot claim subtraction from node reachability alone.
Source typing, operation eligibility, typed-family preservation, and a finite
principal presentation are not premises proved by this induction.
Focused compiler-referee review confirmed the induction and selected-arm
continuation agree with the candidate shallow clauses. Its minor state-threading
finding is closed by the wording above: outer handlers observe each yield under
the live state, including intermediate requests and later resumptions. This
review did not inspect source adequacy or finite abstraction.

This is a proof skeleton, not a completed source theorem. The source machine
and its evaluation-context grammar have not yet been fixed; its capture edges
must correspond to the actual source binding and continuation rules, and the
ordered control simulation must be proved against the source handler clauses.
An escaped continuation must retain edges to captured handler activations,
their state, and lineage even after they leave the active stack. The finite
slot map must be effectively representable and monotone, including unknown
control/state widening; when identity merges make wrapper order uncertain it
must use a sound top transfer rather than infer eligibility. In particular,
`a58eefc3`'s Rust
`Request.resume` closures can only serve as characterization evidence for the
reified source continuation. The `var.run` handler-state ownership edge and
its relationship to abstract cell identity remain to prove. The local
read/weak-write lemma becomes applicable once this general live-graph
simulation establishes its premise; it cannot establish the graph simulation
itself.

A focused compiler-referee review found that node/edge coverage alone is
insufficient: the ordered `H(I(k(r)))` wrapper example changes which handler
sees `p` and the resulting `g` if wrapper order or raw/forwarded status is
lost. The graph clause now explicitly leaves a separate ordered
control-simulation obligation, with activation/lineage edges retained after
escape and top widening when merges lose identity. The review also confirmed
that the `var.run` effect-state bridge is separate from the local heap lemma.
The added condition names the missing theorem; it does not prove it.

A continuation invocation uses the current `H#` and the captured abstract
reference graph; it does not reinstall a heap snapshot. Once a source
resumption is shown to use the current concrete heap (as the frozen runtime
characterization indicates), induction over its source steps can apply the
read/write lemma after every resumed mutation, including the second
multi-shot resume. The induction still depends on proving that continuation
capture and resume preserve `addr#`, the full value/formula packages, active
handlers, and all non-heap state. No whole-continuation simulation follows
from the local heap lemma alone.

If reference identity is observable, `read#`/`write#` are not enough: an
abstract identity comparison must retain a proven must-alias or must-differ
fact, or branch to both equality outcomes. Otherwise the comparison result is
unknown and its dependent control/effect behavior takes the top path. Likewise,
`UnknownCell`/`UnknownStore`/`UnknownState` used by an edge counts as
top-tainted even when the current control slot and continuation are exact;
otherwise an unknown store-dependent branch could escape the fallback.

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
abstract edge holds when its control point, a pending wrapper, or a value/store
location/state component used by the edge is represented by `TopControl`,
`TopKont`, `UnknownValue`, `UnknownCell`, `UnknownStore`, or `UnknownState`.
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
satisfies the top-taint predicate, then some `(A', Obs#) ∈ step#(A)` satisfies
`κ' ∈ γ(A')` and, for every concrete offer `o ∈ Obs`, some `ô ∈ Obs#`
satisfies `CoverObs(o, ô)`. Silent edges have empty `Obs`. This labelled-edge condition covers
requests that are handled and disappear before the successor state.

When the top-taint predicate holds, the abstract transfer first installs the
complete top summary on the affected state/value/control coordinates before
branching, then `step#` preserves or widens it across each transition:

| Concrete transition | Required abstract transfer when the full top summary is present |
|---|---|
| A request is offered, then matched or forwarded | Before either branch, put every possible `TopObs(handler, operation, family, origin, lineage, scope, blockers)` in `Obs#` for all local/unknown handler destinations; retain `TopKont`/`⊤Eff` in the successor. A fact stored only in `A'` does not cover an offer handled on this edge. |
| Catch entry/exit, arm entry/exit | Retain `TopKont`/`⊤Eff` and fan top request, scope, and blocker facts to every possible handler slot. |
| Raw or forwarded continuation resume | Preserve top on the continuation slot; forwarded resume additionally retains the captured `H` wrapper possibility. |
| Read/write or identity test on live state | For exact points-to/state targets, update/read the represented `Σ#` alternatives monotonically; for `UnknownCell`/`UnknownStore`/`UnknownState` or uncertain identity, take the top-tainted transfer and retain top heap/non-heap state, control, value, effect, and offer consequences. |
| Return, closure/thunk construction, storage, or escape | Copy top latent row and top provenance to every result slot that may capture the continuation; otherwise use `UnknownValue`. |
| Call, force, or recursive re-entry | Load the top value summary and emit top observations under every possible current handler slot. |
| Scheme instantiation or imported call | Do not freshen away top; instantiate/export `⊤Eff` and top provenance, or widen to `Unknown*`. |

This transfer table is sufficient for top-tainted edges if the concretization
and finite-interface premises hold: the successor `Σ#` covers the concrete
heap and non-heap state, and the next concrete control point, reachable value,
request observation, and effect all lie in the abstract successor. For an
unknown state read/write/branch, `Σ#` retains `UnknownStore`/`UnknownState` and
the top behavior summary; it cannot reset state to the pre-edge value.
Induction over finite labelled paths proves `γ` coverage for executions after
loss; it does not prove how a non-top `KontFact` is computed or when it must
widen. Escaped roots and imported open rows are part of the induction, not
separate post-processing.

#### Exact-or-top wrapper-step simulation target

The ordered wrapper rule and the top fallback combine into a conditional
one-request simulation for this fragment. Give an abstract control either an
`ExactSpine(W, Snapshot)` tag or `TopControl`:

- Use `ExactSpine` only when every handler reference in the active wrapper
  spine and captured continuation is tied to one unambiguous dynamic activation,
  the wrapper order is represented without truncation, and the request's
  operation, typed family arguments, origin, lineage, scope evidence, and
  needed value/continuation slots are exact. Dispatch it through the ordered
  wrapper transfer above.
- Otherwise dispatch the entire step through `TopControl`: emit `TopObs`
  before branch selection, retain `TopKont` and `⊤Eff`, and cover possible
  arm/value/continuation destinations by top summaries.

Here a concrete `request-dispatch` edge ends before evaluating an operation
arm body. On a match, its endpoint is an `ArmEntry` control with the payload,
raw continuation, inactive matched handler, and surviving outer context. On
all-forward, its endpoint is a forwarded `Request` with the wrapper continuation
constructed above. Requests and effects emitted while an arm body later runs
belong to subsequent edges. The top dispatch edge covers every possible
`ArmEntry` or forwarded-`Request` endpoint; its top effect/provenance summary
also persists into subsequent arm/continuation edges.

Assume the `ExactSpine` tag agrees with the concrete ordered activation stack,
the untouched parts of the state remain related, and `Eligible` plus scope
observations agree for those exact activation references. Assume also the
top-edge simulation and finite-interface premises for every `TopControl`
state. For a concrete request step from `κ ∈ γ(A)`,
case analysis on the tag gives an abstract successor `A'` and observation set
`Obs#` such that:

```text
κ' ∈ γ(A')
∀ o ∈ concrete_offers(κ → κ'), ∃ ô ∈ Obs# . CoverObs(o, ô)
```

In the exact case this is the finite-nesting equation plus identity
observation; in the top case it is the `TopObs` coverage argument. Multiple
resumes reuse the immutable exact spine or top summary and take a union of
successor/observation alternatives, without recording a use count. This
conditional lemma closes only one request-transformer step for exact wrapper
spines or widened states. It does not prove that a source program is mapped to
the right tag, that values/handlers stay related across all transitions, that
the family-row/effect-slot coupling holds, or that `Drop` is sound; those
remain full-machine obligations.

#### Finite-carrier proposition

For one fixed finite checked source and finite interface declarations, fix
finite sets of handler, arm, continuation, value/thunk allocation, heap-cell,
non-heap-state, operation, family, origin, boundary, control, and effect
slots. Open or unenumerated imported families map to `UnknownFam`/`⊤Eff`;
untracked cells and mutable state map to `UnknownCell`/`UnknownStore` and
`UnknownState`; unenumerated interface destinations map to the corresponding
`Unknown*` slot. Fix `K < ∞` for the bounded stack and lineage suffixes. Then
the abstract carrier described above is finite:

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
- The abstract live store is a finite map from the finite cell slots plus
  `UnknownCell` to subsets of the finite value facts, together with finite
  non-heap state facts plus `UnknownState`. Its powerset is finite; strong or
  weak update policy affects precision and transfer correctness, not this
  cardinality argument.
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

#### Receiver-grant transport through an ordinary helper: focused probe

A fresh paired source probe inserts an unannotated-effect helper call inside
the function that receives a callback:

```yu
act choose:
  our reject: () -> int
my invoke(f: () -> [_] int): int = f()
my inner(f: () -> [choose] int): int = catch invoke(f):
  choose::reject(), _ -> 2
  _ -> 20
my outer(f: () -> [choose] int): int = catch inner(f):
  choose::reject(), _ -> 1
  v -> v
outer(\() -> choose::reject())
```

The frozen checker accepts it and the interpreter returns `[2]`, so the inner
catch handles the callback request even though the invocation passes through
`invoke` whose own callback row is wildcard. In the paired source, changing
only `inner`'s callback row to wildcard `[_]` makes the outer catch handle it
instead, returning `[1]`. The outer and inner operation handlers are both
complete for `choose::reject`. This is evidence that an explicit concrete
contract on the receiving function remains effective through an ordinary
helper call inside that function; the helper's wildcard contract does not
erase the receiver's already-established visibility. Without that concrete
receiver contract, the nested inner handler does not gain visibility from
family equality or dynamic nesting alone.

This narrows a possible source grant rule to an activation-scoped capability
introduced by the receiving function's concrete callback parameter contract,
which nested handlers may use during that function activation. It does not
prove that the capability can be transported through returned closures,
independent scheme instantiations, or callbacks passed onward to another
receiver. The closure-escape probe immediately below is a conflicting boundary
case: the same concrete contract accompanies an escaping returned closure and
the frozen implementation leaves the caller request unhandled. Keep the source
claim and the runtime observation distinct until escape and marker semantics
are resolved independently.

The temp programs were `/tmp/yulang-intrusion-boundary-grant-helper.yu` and
`/tmp/yulang-intrusion-boundary-no-grant-helper.yu`. Focused interpreter roots
were `[2]` and `[1]`; the env-gated scratch guard trace for the concrete case
shows the inner operation arm matched without a skip. No repository compiler
code or frozen checkout source was changed by this probe.

#### Partial-application order stress on the receiver-grant candidate

The earlier tuple result probe changed two things at once: it added a curried
ordinary argument before the callback and changed the result shape. A minimal
pair now isolates argument order while keeping the result scalar, both
callback contracts concrete `[choose]`, the wildcard helper, operation, and
complete handlers fixed.

With callback second:

```yu
my inner(x: int, f: () -> [choose] int): int = catch invoke(f): ...
my outer(x: int, f: () -> [choose] int): int = catch inner(x, f): ...
outer 10 (\() -> choose::ping())
```

the outer arm runs, returning `[9]`. With callback first:

```yu
my inner(f: () -> [choose] int, x: int): int = catch invoke(f): ...
my outer(f: () -> [choose] int, x: int): int = catch inner(f, x): ...
outer (\() -> choose::ping()) 10
```

the inner arm runs, returning `[2]`. In the latter source, the request reaches
the inner catch with its `HandlerBoundary` unblocked; in the former the inner
boundary is blocked and the outer boundary handles it. The original polymorphic
tuple stress still returns `((9, 10), (9, "s"))` at two independent
instantiations when the ordinary value argument precedes the callback.

The callback parameter's position in a curried function is therefore a
discriminating observable for the frozen runtime's grant/marker behavior. The
mono dumps show the callback contract materialized at different stages. The
frozen `specialize2::emit` path gets the argument contract from the current
callee's call-spine index, then passes it to the argument boundary wrapper;
the index counts already-applied arguments. The hygiene collector translates
`PreserveMatchingPath` contract markers into carry-after-frame markers. The
runtime trace then distinguishes the cases: for callback-first, carried
markers expose the inner guard at the inner boundary; for callback-second,
the request has only the outer guard and the inner boundary is blocked. This
locates the route difference in staged contract/adaptor marker transport, but
does not justify that transport semantically. It is a counterexample to the
candidate that receiver-local concrete grants alone determine eligibility,
not a soundness counterexample to the Oracle. The successor needs an
independent source rule for staged argument receipt and grant lifetime, or a
concrete soundness/principality conflict before it can choose a different
route.

Frozen source locators (scratch checkout `a58eefc31e22141574b6f20c6a5748151c6d79f1`):
`crates/specialize/src/specialize2/emit.rs` lines 257-265, 1149-1182, and
1209-1219 select the contract by call-spine argument index and pass it to the
argument boundary; `crates/specialize/src/hygiene.rs` lines 69-90 translate
contract resume policies into markers; `crates/specialize/src/lib_support/boundary.rs`
lines 106-112 builds the `FunctionAdapter`. These locations characterize the
frozen implementation only. No corresponding algorithm is adopted as
successor authority.

#### Partial application across a handler boundary

The same argument-order pair was staged so callback receipt and execution
occur in different expressions. In the callback-first variant,
`partial = outer callback` is formed before the caller's `catch`, then
`partial 10` is invoked inside that caller handler. It returns `[2]`, from the
inner function's arm. In the callback-second variant,
`partial = outer 10` is formed first and the callback is supplied under the
caller's `catch`; the request bypasses both function-local handlers and the
caller returns `[7]`.

The mono trees explain where the frozen representation differs. The first
variant has a `FunctionAdapter` around the residual partially applied
`outer` function, carrying the callback argument marker, as well as an adapter
around the callback. The second variant's residual `outer 10` has an empty
hygiene adapter; the callback gets its argument adapter only when later
supplied. Runtime tracing confirms the first request has carried markers that
expose the inner guard and the inner boundary is unblocked. In the second,
the request has only the caller guard; the inner and outer function boundaries
are blocked, and the caller boundary handles it.

Direct-application controls under the same caller catch return the same roots:
`catch (outer callback 10)` returns `[2]`, while
`catch (outer 10 callback)` returns `[7]`. Their mono trees show the same
parameter-position-associated adapter distinction. Therefore the presence of
a named partial value is not itself necessary for the route difference. The
staged pair characterizes how the adapter is represented across the residual
function boundary, but it does not isolate that boundary crossing as the
cause; argument position and adapter placement still vary together.

This demonstrates that grant eligibility cannot be summarized only by the
receiving activation or by a marker on the callback value: argument position
changes the frozen result in both direct and staged applications. It is still
only Oracle characterization. The successor must define from source
evaluation and the chosen effect abstraction whether and how a callback
contract constrains the residual function at each currying stage, then show a
semantic preservation argument for the inferred route; the mono adapter
topology is not that argument.

Fixtures:
`/tmp/yulang-intrusion-grant-callback-first-staged.yu` and
`/tmp/yulang-intrusion-grant-callback-second-staged.yu`. Both passed `check`
and interpreter execution; roots were `[2]` and `[7]`. `--mono` dumps and
`YULANG_INTRUSION_GUARD_TRACE=1` showed the adapter and guard differences
described above. These additional probes further falsify receiver-local grant
sufficiency; they do not establish an Oracle soundness conflict. Direct-catch
controls `/tmp/yulang-intrusion-grant-callback-first-direct-catch.yu` and
`/tmp/yulang-intrusion-grant-callback-second-direct-catch.yu` also passed
`check`; the first returned `[2]`, and the second `[7]`.

#### Conditional pure-currying trace law

A useful source-semantic law to test independently is pure-currying
permutation invariance. Let `v` and `w` be values whose evaluation emits no
requests, and let the callback argument be used only after both parameters
have been received. Under ordinary call-by-value beta semantics,

```text
((λx. λf. body(f)) v) w
((λf. λx. body(f)) w) v
```

reduce to the same `body(w)` configuration. If effect annotations constrain
latent support but do not change runtime dispatch, both configurations enter
the body with the same handler stack and must have the same request trace and
handler route. This is a conditional semantic law, not yet an approved Yulang
rule; the source authority has not defined whether callback contracts affect
dispatch.

The immediate callback-first/callback-second fixtures instantiate this law's
shape: the reordered `int` and lambda arguments are pure values, the same
callback is invoked under the same nested complete catches, and both programs
pass `check`. The frozen Oracle returns `[2]` (inner catch) for callback-first
and `[9]` (outer catch) for callback-second. Thus, if the successor adopts
ordinary pure beta/currying invariance, this is a concrete Oracle runtime
compatibility difference to record; it is not an acceptance-capability
difference, since both sources are accepted. The staged pair further shows
that placing the callback receipt before versus after construction of a
residual partial function changes the frozen route. No weight law follows
from these observations.

The previous binary framing (“static row bound” versus “dispatch grant”) was
too coarse. The user's `intrude-effect-hygiene` design explicitly separates
type identity/support from handler visibility evidence: the same parent may
have plain and boundary-hidden occurrences, and path history must not be
collapsed into one vertex-local value. The successor therefore needs distinct
meanings for (1) typed effect support, (2) boundary/hygiene evidence, and
(3) operational handler selection. A row family alone cannot authorize
`Drop`; a visibility proof alone cannot establish that a request belongs to
the handler's typed family or covered operation.

#### Orthogonal effect support and handler visibility (unselected)

The current source authority defines the `EffectRowType` syntax shape but
explicitly leaves row meaning, effect inference, and lowering undefined. The
research cannot infer visibility or dispatch from row syntax alone. A
candidate elaboration for an effect occurrence keeps separate coordinates:

```text
EffectFact = (typed_family_and_operation,
              support_constraint,
              ordered_boundary_evidence)
```

The support coordinate bounds possible requests. Boundary evidence records
how that occurrence crosses source boundaries and is transported by its own
capture-avoiding binder map. A handler can subtract a family only when every
possible typed request is both covered and eligible under the independently
defined evidence/activation relation. Runtime selection must then implement
the same source rule; otherwise the row proof and execution diverge. Whether
and how an explicit callback annotation contributes boundary evidence remains
open, and must not be implemented as `annotation has family => grant bit`.

The concrete-versus-wildcard helper probe shows that annotation form is
correlated with frozen handler routing, but does not establish whether that
correlation comes from a support bound, boundary evidence, or their transport.
The callback-order probes show that the same family can route differently
when its callback occupies a different curried position. The conditional
pure-currying law applies only if source elaboration gives the two occurrences
equivalent boundary evidence; the evidence identity and ordered path must be
compared before claiming the law's premise. The immediate programs both pass
`check`, so the observed route difference is not presently an acceptance
loss, unsound scheme, or nonprincipality result. No repeated-push/shared-pop
routing theorem follows from these observations.

The proof target is now: define source elaboration for each coordinate;
define visibility as a relation over request lineage and handler activation;
prove transport of that evidence through calls, closures, partial
applications, SCC generalization, and independent instantiation; and prove
that every `Drop` certificate names the activation that actually handles all
requests it removes. `intrude` only transports the established boundary
evidence; it does not invent boundary opening/closing or route rules. These
requirements follow the user's existing draft and do not select a final
dispatch policy or authorize implementation.

An architect, compiler-referee, and specification audit agree that this split
is only a candidate and neither obvious annotation reading can be selected
yet. If annotations constrain support but are dispatch-inert, the frozen
concrete-versus-wildcard helper pair is already a runtime routing difference
(`[2]` versus `[1]`), though not a final-acceptance difference. If a concrete
callback contract introduces stage-scoped visibility evidence, its receipt
point, capture in residual partial functions, and expiration on
call/return/escape/re-entry still need a source rule and preservation proof.
The callback-order pair also remains a runtime divergence (`[2]` versus
`[9]`), not a soundness, principality, or acceptance counterexample; its pure
currying premise fails until elaboration proves equal boundary evidence.

Review rejects both premature pure-currying invariance and a receiver-local
family grant bit. Neither the current transfer-table fallback nor a finite
probe matrix proves unbounded source-to-trace simulation or principality. The
smallest next proof step is a source transition judgment that makes typed
callback receipt at each curried stage and residual-closure capture explicit,
while keeping request support, ordered boundary lineage, and live handler
activation distinct. It must define handler eligibility and the shallow
raw-versus-forwarded continuation transition, then prove that the route
abstraction over-approximates every finite source trace. Only after that rule
and its compatibility deltas have independent review is a user choice between
any remaining semantic alternatives well-posed.

#### Parameterized source-transition skeleton for handler visibility

The smallest operational object needed by the next proof can be stated without
assigning meaning to Oracle weights. This is a conditional skeleton; it is not
a selected source semantics because the visibility relation below remains
undefined.

```text
RuntimeState = (expression, environment, ordered active HandlerId stack,
                captured boundary evidence)

RequestObservation = (typed family instance, exact OpId, origin,
                      ordered boundary-evidence lineage,
                      current active HandlerId stack)

FunctionStage = (static function/parameter binder, stage index,
                 parameter contract, residual closure)
```

The raw trace needs an occurrence-local lineage, rather than one visibility
slot on a family or type variable. A small event vocabulary for the missing
transport proof is:

```text
BoundaryEvent ::= Provided(provider_site)
                | Received(parameter_stage, argument_index, contract_binder)
                | Captured(partial_closure_site, dynamic_closure_id)
                | Invoked(parameter_stage, dynamic_call_id)
                | Forced(thunk_site, dynamic_force_id)

BoundaryLineage ::= [BoundaryEvent]
```

The source/provider/stage/contract/closure *sites* and type binders are static
identities. `dynamic_closure_id`, `dynamic_call_id`, and `dynamic_force_id` are
fresh evaluation identities; they cannot be substituted by a compile-time
`Theta` map or shared across independent evaluations. A value adapter or
partial closure transports the ordered `BoundaryLineage` attached to that
value. The request occurrence adds its own typed family and exact operation
without replacing the path by family equality. This event vocabulary describes
what a proof must observe, not which events create, mask, or discharge
visibility. Any finite quotient used by inference must show that it preserves
all `Visible` and `Drop` decisions over every finite trace; raw histories must
not be collapsed to a parent-local state merely to force a finite domain.

Function application is staged. At each argument receipt, the source rule
resolves that stage's parameter contract and records its boundary-evidence
transform on the received value or adapter. If arguments remain, the residual
callable captures the adapted arguments and their evidence; invoking that
residual callable transports the captured evidence into the eventual body.
This says where the semantics must account for callback-first/callback-last
and partial application. It deliberately does not say that a concrete row
creates a grant, that a wildcard erases evidence, or how long a receipt token
authorizes a handler.

Entering a catch creates a fresh dynamic `HandlerId` and pushes it on the
active stack. A request records its typed family, exact operation, origin and
ordered evidence lineage. For a direct nested-catch stack, selection is the
first inner-to-outer activation whose exact-operation coverage holds and whose
`Visible(lineage, handler_id)` predicate holds; the stack-order part follows
from the shallow transformer as recorded in
`notes/progress/2026-09-30-intrusion-shallow-handler-trace-calculus.md`,
"Ordered active-handler stack". `Visible` remains open. If a handler matches,
its arm receives the raw continuation, without that handler reinstalled. If
no handler is selected, the request is forwarded; resumption wraps the saved
continuation so this handler remains active for the later suffix. The
selection-order lemma does not use the Oracle's runtime guard implementation.

Static binder identities in captured evidence use capture-avoiding transport;
dynamic handler activations are fresh runtime identities and are never copied
from compile-time IDs. Type substitution changes typed family payloads but
does not rewrite operation identity or collapse evidence lineage. Static
analysis may project requests to finite family support, but it may certify
`Drop(H,F)` only if every represented typed request and route maps to an exact
covered operation and a runtime-selected activation equal to `H`; unknown
lineage blocks the drop. Raw-continuation-only effects remain in the
continuation/arm latent bound rather than being fabricated as offers to `H`.

The candidate simulation obligation is now explicit: every finite runtime
request transition must map to a typed request fact with its source lineage;
every runtime-selected handler must be justified by the candidate `Select`
and `Visible` relations; and every removed family must be absent from
all outward finite traces, including forwarded suffixes and arm effects. A
least-solution/principality proof additionally needs a finite compositional
domain whose derivable bounds correspond to source judgments. This skeleton
does not prove any of these obligations, choose `Visible`, resolve the
concrete-versus-wildcard or callback-order Oracle differences, or authorize
implementation. It narrows the missing design decision to the source meaning
and transport of stage evidence plus its handler-activation relation.

#### Empty-row annotation control

The route pair was also checked with `[] int` result annotations on both
`inner` and `outer`. Both callback orders still pass `check`, and the
interpreter still returns `[2]` for callback-first and `[9]` for
callback-second. As a control, a direct unhandled operation in a function
annotated `: [] int` fails with `effect filter mismatch: choose is not allowed
by []`; changing that annotation to `: [choose] int` passes. These source
observations show that the empty row constrains residual effects and that the
nested catches discharge the effect filter in both order variants. They do
not explain or authorize the different handler arm: dispatch is a separate
semantic dimension from the residual row bound.

Fixtures:
`/tmp/yulang-intrusion-grant-callback-first-pure-result.yu`,
`/tmp/yulang-intrusion-grant-callback-second-pure-result.yu`,
`/tmp/yulang-intrusion-effect-row-empty-result.yu`, and
`/tmp/yulang-intrusion-effect-row-concrete-result.yu`. The two nested cases
pass `check` and return `[2]`/`[9]`; the direct empty-row case is rejected,
and its concrete `[choose]` counterpart passes. This is characterization of
the frozen Oracle only.

The independent-use case checked successfully; both interpreter runs and
`--poly-raw` / `--mono` dumps completed. Relevant temp fixtures are
`/tmp/yulang-intrusion-grant-independent-uses.yu`,
`/tmp/yulang-intrusion-grant-independent-inner-only.yu`,
`/tmp/yulang-intrusion-grant-outer-fixed-tuple.yu`,
`/tmp/yulang-intrusion-grant-scalar-extra-arg.yu`, and
`/tmp/yulang-intrusion-grant-scalar-callback-first.yu`. The failed earlier probe
that put the type variable in the effect-family argument panicked at the
Oracle's `one stack id must not use multiple families` assertion; it is not
used as evidence here. This also leaves a separate diagnostic-quality issue to
classify if such family-argument polymorphism lies in the supported source
envelope.

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

#### Typed family evidence transport (conditional lemma)

When same-path family heads meet in the frozen specification's set, split,
filter, or stack-check operations, their arguments receive invariant ordinary
constraints; two unrelated occurrences in separate rows do not constrain one
another. Path equality alone never discards payload types. For well-formed,
same-path, same-arity heads, a conditional candidate grant check generates:

```text
InvMatch(F<α₁,...,αₙ>, F<β₁,...,βₙ>)
    = ⋀ᵢ (αᵢ <: βᵢ  and  βᵢ <: αᵢ)
```

Different family constructors do not match. For a capture-avoiding type
renaming `θ`, applying the *same* `θ` to request, callback effect, and grant
evidence maps each generated argument constraint to its renamed constraint:

```text
θ(InvMatch(F<α>, F<β>)) = InvMatch(F<θ(α)>, F<θ(β)>)
```

This establishes only syntactic commutation of constraint generation with a
common renaming/substitution. It does not prove that a grant is in scope, that
solving preserves its evidence, or that independently freshening grant and
request arguments is sound. A scheme-instantiation proof must use the same
binder map for family arguments in effect rows and their associated grant
evidence, while preserving separate binder ownership where the source
semantics requires it. Alpha-renaming invariance follows conditionally for
injective capture-avoiding renamings; solution reflection for general solved
substitutions and principality remain separate obligations. This transport
lemma is a small dependency of the intrusion/hygiene composition, not an
eligibility or grant-lifetime decision.

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

#### Callback effect in a returned closure: independent row-preservation lemma

The lost effect in `maker` does not depend on which handler is eligible later:
the body of `maker` contains no handler, and evaluating the returned closure
`\_ -> f()` produces a function value whose later call performs `f()`. Let
`E` be a sound latent request-support bound for `f`. The ordinary compositional
typing fragment required for sound closure effects is:

```text
Γ, f : Unit -[E]-> Int ⊢ f () : Int ! E
Γ, f : Unit -[E]-> Int ⊢ (\_ : Unit -> f ()) : Unit -[E]-> Int ! ∅
Γ ⊢ maker : (Unit -[E]-> Int) -[∅]-> (Unit -[E]-> Int)
```

Application carries the callback's latent bound into the body. Closure
construction is immediate-effect-free but retains that bound on the returned
arrow; calling `maker` itself only returns the closure. For every finite trace
of a later call, the request events from `f()` are included in `E`, so
replacing the returned arrow's latent row by a strict subrow is unsound. If
`E` is unknown/top, it remains unknown/top. This argument does not require
continuation-use counts or exact continuation-sensitive inference.

Any handler subtraction is a separate operation at the later invocation
site. It must use typed coverage and the source-derived visibility evidence
for that particular handler activation; it cannot mutate the returned
function scheme retroactively. SCC generalization and each use-site
instantiation must map the callback and returned-arrow effect binder
consistently, while transporting hygiene/boundary evidence separately as
required by the intrude effect-hygiene design.

The concrete `[choose]` closure fixture violates this minimum rule in the
frozen Oracle: its accepted `maker`/`delayed` schemes erase `choose` from the
returned arrow, while forcing `delayed` emits `choose::reject`; the direct
closure control retains `[choose]`. This is a soundness conflict in the frozen
inferred scheme itself, not merely a disputed handler-arm choice. The
successor must preserve `choose` on the returned arrow. Whether the enclosing
caller remains accepted is still conditional on handler eligibility and the
chosen coarse continuation abstraction; this lemma does not claim an
unconditional final-acceptance delta.

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

#### Conditional soundness of route-certified shallow subtraction

The direct-tree transformer above gives a general soundness target beyond the
four individual witnesses, while remaining independent of any weight
representation. Fix one shallow activation `H`, a finite source tree `C`, and
`E = supp(C)`. Let `A` be a uniform sound immediate-effect bound for every
value- and operation-arm execution at every reachable activation, including
arm continuations after their own emitted requests. Applying any raw
continuation contributes its declared latent bound `E`; if an arm returns or
stores a continuation, the result-value summary must retain that latent bound
for later calls. A route certificate for family `f` is admissible for
subtraction only when it is complete for every contribution of `f` and every
reachable visit to `H`:

1. every current or forwarded offer of `f` is covered by the exact operation
   arm and eligible at that activation;
2. every raw-continuation route, including the raw side of a mixed route, is
   represented by the matched raw `k` latent bound and is contributed to `A`
   on invocation; returned continuations retain that latent bound for later
   calls; and
3. no contribution has an unknown or unclassified route.

Let `Drop_H` contain only families with such certificates. Then the candidate
subtraction law has the conditional immediate-trace soundness property

```text
supp(H(C)) ⊆ (E \ Drop_H) ∪ A.
```

Proof sketch by induction on finite executions of the shallow transformer.
At an unmatched or ineligible request, that request is forwarded, so its
family cannot be removed by condition 1; forwarding keeps `H` around the
suffix, and the induction hypothesis applies after an outer handler resumes
it. At a matched request, condition 1 permits removing its covered request
from the residual. The arm runs outside `H`, and its trace is covered by `A`.
If it invokes the raw continuation, the uniform arm bound `A` charges the
whole pre-handler bound `E`, which covers every request in that suffix without
reinstalling `H`; if it does not invoke `k`, that suffix contributes no
immediate trace. Unknown routes fail condition 3 and therefore remain in the
residual. The `Return` case contributes only the value-arm bound in `A`.
Finite-prefix induction handles any finite number of forwarded resumptions.

This establishes soundness only for the declared direct request-tree
semantics, provided the route certificate and arm/latent bounds satisfy the
premises. It does not construct certificates from source constraints, prove
that route evidence is finite under calls/escape/re-entry, prove leastness or
derivation correspondence, or establish Oracle-equivalent final acceptance.
In particular, `E` on a raw `k` is intentionally coarse: it may retain a
family after an exact suffix that emits no request. That is allowed by the
chosen abstraction and requires no continuation-use tracking.

A focused compiler-referee review found no finite-trace counterexample under
these premises. It required the uniformity now stated for `A` across reachable
activations and arm continuations, and clarified that mixed offer/raw routes
must satisfy both obligations. This review covers only the conditional direct-
tree lemma; source lowering, route-certificate construction, the finite
quotient, visibility correctness, and returned-callable correspondence remain
open.

#### Conditional monotonicity of route-certified subtraction

The remaining fixed-point obligation can be split into a small support lemma
and the still-open source-evidence theorem. Fix one handler activation and
consider a set `O` of route-classified family contributions. Each contribution
has immutable typed identity and route evidence. For a family `f`, define
`Safe_H(o,A)` to mean: an offer contribution has complete coverage and
visibility evidence at every represented visit; a raw-only contribution has
its `f`-effect charged into the arm summary `A` on every invocation of raw
`k`, and every returned/exported value preserves the corresponding latent
bound; and no unknown/unclassified alternative is present. A mixed
contribution must satisfy both offer and raw obligations. Define

```text
Drop_H(O,A) = { f ∈ support(O) | for every o ∈ O with family(o)=f, Safe_H(o,A) }
Result_H(O,A) = (support(O) \ Drop_H(O,A)) ∪ A
```

Assume evidence is stable when contributions are added: old contributions
keep their family, route alternatives, and offer-certificate validity, and
adding a contribution cannot rewrite or discharge an old offer obligation.
Also assume `O₁ ⊆ O₂` and `A₁ ⊆ A₂`. Then
`Result_H(O₁,A₁) ⊆ Result_H(O₂,A₂)`. For a family already in `A₁`, this follows
from `A₁ ⊆ A₂`. For a family in the first residual, it remains in the second
residual unless the second certificate drops it. A formerly unsafe offer or
unknown route cannot become safe under stable evidence. The only old
obligation that can become safe as `A` grows is a raw-only obligation; its
definition requires that the corresponding family now belong to `A₂`, so the
family remains in the second result. Thus the combined result, rather than
residual subtraction alone, is monotone. If `A_H(O)` is monotone in `O`, the
composite `Result_H(O,A_H(O))` is monotone. This argument does not assume
Oracle's left/right weight routing or treat family support as the route proof.

The stability premise is essential and not yet derived from source solving.
If type refinement removes an `Unknown` route or changes the admissible target
set, evidence is not merely extended by inclusion; the relation must model
that refinement explicitly and prove a corresponding solution/leastness
result. The lemma also requires complete contribution enumeration, stable
handler activation classes, and sound raw-value latent summaries. It proves
neither those properties nor monotonicity of the coupled type/effect operator.
For the separate open-world `TopEff` abstraction, any unknown or unclassified
route sets the input and result to absorbing `TopEff`; only a proved finite
support enters this finite-family theorem. This is the Top transfer premise,
not a consequence of the finite-set proof. The result isolates one algebraic
obligation for the eventual source-to-constraint proof, rather than claiming
that the current conditional transfer is already a principal recursive
inference system.

A scoped compiler-referee review found that the first version did not require
raw-only continuation effects to be charged into `A`; a raw suffix could then
be unsoundly dropped. The revised `Safe_H(o,A)` condition and combined-result
monotonicity proof close that counterexample. The closure review found no
remaining issue under the stated evidence-stability and monotone-arm premises.
This review does not establish those premises from source constraints.

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

#### Architecture delta: source annotation does not yet select a stable domain

A bounded architecture review of the source-to-domain bridge found that the
frozen Oracle facts above do not establish a general rule
`ordinary annotation → Value(A)` or `AnnType::Effectful → Susp(U,A)`. The
lowering path creates effect endpoints/stacks; lambda specialization binds a
runtime shape from a materialized graph effect; `runtime_shape` chooses plain
versus thunk by syntactic materialized purity; application then adapts based on
the actual argument shape. The missing invariant is a relation carrying one
stable accepted boundary from source annotation through constraints,
generalization/instantiation, shape solving, and adaptation. The explicit
`int` / `[_] int` result is evidence for those two characterized cases only.

The bounded trace theorem remains conditional on a boundary already selected:
for suspension `C` with `supp(C) ⊆ U`, strict adaptation emits
`supp(C)` before body entry; an ignored deferred argument emits nothing; a
forced deferred argument emits `supp(C)` in the body. A reusable
`ret_eff ≥ U` is sufficient only when every admissible suspended input is
uniformly bounded by `U` and the force path does not locally handle away part
of that bound. It is neither necessary nor shown principal. A concrete open
bridge to check is that semantically pure constraints may materialize as an
empty row or an open variable even though `runtime_shape` distinguishes them
syntactically; subtype, instantiation, or adapters may likewise alter the
boundary. No exact continuation-sensitive inference, linear/affine typing, or
usage tracking follows from this gap. The next safe proof is restricted
source-to-elaboration correspondence for the annotated pair through
materialization and adaptation, followed by the parameterized force-bound
lemma. This review changes no candidate rule and grants no implementation
authority.

#### Restricted endpoint and mono-shape correspondence: split evidence

The finalized endpoint/materialization evidence for the annotated pair is
recorded in
`notes/progress/2026-09-30-intrusion-oracle-latent-effects.md`, “Finalized
inference-endpoint follow-up”: the exact probes report `Bot`/`Top` and
`Never`/`Any` for the ordinary and wildcard-effect parameters. The frozen
`specialize2::lambda_type` binds a parameter using `runtime_shape`, which maps
a pure effect to a value and a non-pure effect to a thunk. This supports the
corresponding runtime domain for those finalized predicates.

The mono probe separately observed `ForceThunk` on the strict call and
`MakeThunk` containing the read's `ForceThunk` on the deferred call. The
scratch test body was removed, so its precise entrypoint is not preserved in
the record. Frozen `specialize/src/lib.rs` routes both public `specialize` and
`specialize2` through `specialize2::specialize`; however, that does not rule
out the legacy `Specializer::specialize_roots` API having been used by the
probe. Do not claim one end-to-end pipeline from these separate records.

For the `specialize2` path specifically, the application transfer is
`specialize2::task_solver::apply_type`: a pure `parts.arg_effect` uses
`consume_expr_value`, while a non-pure one uses `consume_expr_computation`;
the callee consumer is then related to actual and expected materialized
occurrences. The `specialize2::emit` path creates `ForceThunk` through
`force_emitted_value_thunk` and `MakeThunk` through
`make_thunk_from_computation`. Separately, runtime `adapt_value` forces a
thunk-to-value boundary and preserves thunk-to-thunk adaptation. That runtime
function describes adapter behavior; it is not evidence that the removed
probe executed that adapter path. The older `solve/expr_solver.rs` application
path is not the matching path for `specialize2` and is not used to connect the
probe's output here.

The conditional force/ignore consequence remains supported by the generated
mono shapes and runtime step definitions: if the observed `MakeThunk` suspends
the read until force, the ignored deferred call emits no request; the observed
`ForceThunk` in the strict call emits the read request before body entry. The
probe specialized but did not execute either program. This is useful
characterization evidence, not a joined inference-to-runtime simulation proof.
It requires no continuation-use counting: the example delays an ordinary
argument computation and the body either ignores or forces that value. Exact
trace support remains the soundness reference, while a successor may use a
sound coarser compositional bound with principality stated relative to that
bound.

An independent compiler-referee delta review closed the mixed-pipeline finding:
the historical endpoint/materialization observations are now separate from
the mono-shape observation; the `specialize2` application and emission path is
cited on its own; and runtime `adapt_value` is not represented as an observed
step in the removed probe. The reviewer confirmed the described
`specialize2` branch and helper links, but explicitly did not recover the
historical probe entrypoint or certify one end-to-end chain. Treat those
outputs as separate characterization evidence until that provenance gap is
closed.

The two remaining local obligations at this point were a static transfer/
emission lemma for the selected `specialize2` path and a force-bound lemma for
an already selected suspended domain. The following subsections record both.
The force bound assumes each admissible argument computation has latent
support bounded by `U`; each force site charges an abstract bound covering `U`
unless a proved handler transfer removes part, while moving or ignoring the
suspension charges no latent request immediately. This does not state that
`ret_eff ≥ U` is necessary for every individual fixed trace.

#### Conditional specialize2 application-transfer equation

For a solved/materialized function type
`Fun(A, εarg, εret, R)`, frozen `specialize2::task_solver::apply_type`
branches on `Type::is_pure_effect(εarg)`. In the pure branch it consumes the
argument as a value at `A`; the argument's evaluation effect becomes the
immediate `call_arg_effect`, and the callee's runtime argument-effect slot is
pure. In the non-pure branch it calls
`consume_expr_computation(arg, εarg, A)`; the returned constrained runtime
argument effect is placed on the callee consumer, while `call_arg_effect` is
pure at this application boundary. Both branches relate the materialized
callee actual and expected Function occurrences. The produced application
computation has effect
`εcallee ∨ call_arg_effect ∨ εret` and value `R`, then passes through
`runtime_shape`.

This is a code-level transfer identity conditional on the solved function
shape and on `consume_expr_value` / `consume_expr_computation` doing their
declared subtype and effect-constraint work. Lambda binding uses the same
materialized shape convention in `lambda_type`, via
`runtime_shape(arg_effect, arg)`. The emitter then realizes a selected
boundary: for an expected thunk, `boundary_emitted_expr_with_argument_contract`
may pass through an equivalent existing thunk or wrap a computation with
`make_thunk_from_computation`; when an emitted value is thunk-shaped and the
expected boundary is plain, `ensure_emitted_value_with_argument_contract`
emits a `ForceThunk` after its equivalence checks. This establishes internal
consistency among the newer specializer's selected argument mode, call
accounting, and boundary constructors. It does not prove that source
annotations select the right `εarg`, that `εret` soundly bounds latent
execution, or that a captured handler route survives later forcing. The
removed mono probe is not evidence for this equation's execution path. Frozen
source locators are
`specialize2/task_solver.rs:479-565,605-620`,
`specialize2/emit.rs:806-889,891-950`, and
`specialize2/runtime_shape.rs:794-850`.

Exact continuation-sensitive trace support is not required for this transfer.
The soundness obligation is that strict consumption charges an effect bound
covering every forced argument, and deferred consumption retains a latent
bound that every later force charges unless a proved handler transfer removes
it. Principality is relative to the chosen compositional effect abstraction;
the code branch alone establishes neither theorem.

#### Conditional latent-row force soundness lemma

Fix a value/suspension boundary with a latent allowance `U`, and assume its
contract guarantees `supp(C) ⊆ U` for every admissible suspended computation
`C`. For this local lemma omit handlers, adapters, recursive forcing, and
unknown calls. Assume an independent immediate-effect judgment already bounds
every request produced by evaluating the callee, body, or other direct work:
each such step contributes a row `B_step` containing its exact support, and
sequential composition joins that row into `E_now`. This premise is not proved
by the latent-row lemma. Give each evaluated fact a separated immediate row
`E_now` and latent suspension allowance `U`. Moving or returning the
suspension preserves `U` and leaves `E_now` unchanged; ignoring it likewise
adds no latent row. Forcing it joins `U` into the current computation row and
returns the forced value fact. A caller that later forces an escaped
suspension applies the same rule at that force site.

For every concrete immediate trace produced by these transfers, its exact
support is contained in the abstract row: direct work is covered by the
`B_step` premise; a step evaluating `C` adds `U`, which contains `supp(C)`;
non-force suspension steps preserve the exact pending computation and add no
request from it. Sequential composition joins the rows, preserving inclusion.
This proves soundness of the latent-row contribution by induction on the
finite call/force sequence, provided the `LatentCover` invariant holds for
each moved or returned whole value fact. It requires no continuation-use
count or exact suffix correlation.

The lemma does not cover handler subtraction: with a handler, `U` may be
removed only by an independently proved handler-route transfer for that force
site. Nor does it show the source type system enforces the uniform bound,
prove the `LatentCover` invariant through subtyping/generalization/adapters,
or imply that charging all of `U` is the least solution for every source
program. Principality remains relative to the chosen abstract constraints and
their derivations. The lemma is a candidate local preservation result, not
successor authority.

An independent compiler-referee review found that the initial statement
omitted a bound for ordinary immediate requests. The lemma now assumes each
non-suspension step contributes a sound `B_step` joined into `E_now`; the
reviewer confirmed this closes the direct-request counterexample and the
finite-sequence induction under the stated exclusions and `LatentCover`
premise. This does not prove that source inference supplies those immediate
rows or preserves `LatentCover` globally.

#### Conditional source annotation to latent allowance mapping

A bounded architecture review found a possible way to define `U` independently
of handler visibility and frozen Oracle weights, but only after choosing a new
annotation-denotation rule. Under that candidate rule, resolve each effect
head to a canonical family identity. A closed row with resolved heads `H`
denotes allowance `U = H`; an empty closed row denotes `∅`. An open row with
head set `H` and tail `α` denotes `H ∪ Uα`, where an unbounded or unresolved
tail widens to `TopEff`. A wildcard denotes `TopEff` unless a separate proved
bound narrows it. None of these allowances grant handler visibility.

This mapping is not entailed by current Yulang3 authority. The authoritative
syntax page defines `EffectRowType` shape but explicitly leaves row-tail
meaning and effect lowering undefined. Its CST has direct syntactic
`TypeExpression` items and no dedicated row-tail node; semicolon is a literal
delimiter, not a tail marker. The frozen Oracle's `AnnEffectRow` has a separate
tail field and its semicolon lowering and weighted constraints are
characterization evidence only. Do not transfer those rules into Yulang3 by
assumption. Canonical family identity also remains unresolved: textual paths
or aliases cannot be collapsed for support bounds or handler subtraction
without a sound name-resolution relation.

The candidate `Susp` introduction rule must reject or widen any stored
computation whose force support is not covered by its allowance. In
particular, an `out.read` computation cannot be admitted as `Susp(∅,A)` merely
because an annotation spells an empty row. For an open tail, the constraint
must remain valid under every admissible tail substitution; if no sound bound
is known, use `TopEff`. Latent adapter work and nested force steps must also be
included in the stored computation's bound. This constraint-transfer fact is
not yet established.

The target preservation theorem is: for every already evaluated suspension
value `v` produced by well-typed derivations of the candidate rules, each
finite trace of `force(v)` has support included in its `U` in
`Γ ⊢ v : Susp(U,A)`. The proof must establish that the introduction and
adaptation rules really enforce the bound above, including open-tail
substitution and unknown widening. If the source expression `e` that creates
`v` can itself emit requests, its total trace is bounded by
`E_now ∪ U`, where `E_now` comes from the separate immediate-effect judgment.
This theorem excludes handler subtraction; the handler-route proof remains
separate. It neither requires exact continuation-sensitive inference nor
follows from row denotation alone. Both the typing rule and theorem remain
unselected candidate semantics, with no implementation authority.

Independent compiler-referee delta review initially found that the target
force-bound statement lacked a typing/elaboration premise and conflated
suspension-creation effects with forcing. The revised candidate now requires
admission to check the latent allowance under every tail substitution and
includes adapter/nested-force work; it bounds already evaluated suspensions
by `U` and creation traces by `E_now ∪ U`. The referee confirmed the direct
empty-row request counterexample is closed and that this remains an unproved
preservation target. A separate specification review confirmed that
“direct syntactic `TypeExpression` items” matches the syntax authority and
that semicolon/tail and row denotation remain correctly separated.

#### Candidate declarative typing fragment for a selected suspension domain

To make the preservation target falsifiable, consider a small independent
typing fragment. Let `D_eff = P(Fam) ∪ {TopEff}` with subset order and
`TopEff` absorbing join. Write `Pref(c)` for all finite execution prefixes of
computation `c`, including prefixes that end in an unhandled request, abort,
stuck state, or divergence. Define `Γ ⊢ c : A ! E` to require both (1) every
prefix in `Pref(c)` has request-family support included in `E`, and (2) every
returning execution produces a value of type `A`. Nonreturning prefixes still
constrain `E`; result typing is checked separately. Write `Susp(U,A)` for an
already evaluated delayed computation whose result has type `A` and whose
force-prefix support is bounded by `U`. This is a semantic candidate
judgment; current syntax and inference do not yet define it.

The force and introduction rules are:

```text
ρ = capture_env(c)       Γ ⊢ c[ρ] : A ! E       E ⊆ U
supp(Pref(capture(c))) ⊆ E_make       capture(c) does not evaluate c
───────────────────────────────────────────────────────────────  suspend
Γ ⊢ delay(c,ρ) : Susp(U,A) ! E_make

Γ ⊢ e : Susp(U,A) ! E_now
──────────────────────────  force
Γ ⊢ force(e) : A ! (E_now ∪ U)
```

`capture_env(c)` is the environment stored with the delayed body, and `c[ρ]`
is the body under that captured environment. The typing premise must hold for
the stored body, not just the uncaptured lexical expression. `capture(c)` is
the work performed to construct the delayed value, such as evaluating its
captures; `E_make` must bound every request-bearing prefix of that work. The
premise also requires construction not to run `c`.
The force rule is deliberately conservative: it charges the whole allowance
`U`, which bounds every request-bearing prefix of the stored computation,
even if one fixed continuation suffix later emits fewer families. Moving,
returning, or ignoring an already evaluated `Susp(U,A)` preserves `U` and
contributes no latent family to the immediate row. Passing a `Susp(E,A)` to a
formal `Susp(U,A)` requires `E ⊆ U` under every admissible row substitution
and preserves the suspension; a value `A` adapted to `Susp(U,A)` is wrapped
with latent row `∅`.
Passing `Susp(E,A)` to a strict value formal `A` forces it at that boundary
and contributes `E` to the caller's immediate row. Joins on branches and
sequences use the finite row join. No transfer consults handler visibility.

For this fixed-domain fragment, the force-prefix support theorem follows by
induction over finite execution: `suspend` admits only computations already
bounded by `E ⊆ U`, including their nonreturning request prefixes; force adds
`U`; move/return/ignore do not execute the stored body; strict adaptation is
the force case; and deferred adaptation checks subeffect inclusion before
preserving it. Repeated ordinary forces rejoin the same family set
idempotently; no continuation-use count is needed. If constructing an
argument emits immediate requests, they remain in `E_make` outside latent
`U`. The result value on a returning force path must preserve any nested latent
facts in its payload type `A` for later force sites. This fragment assumes
capture substitution preserves the body's type/effect bound and the captured
environment's whole latent facts; proving that property for source lowering
and mutable or opaque captures remains open.

This is a trace-denotational fragment, so its local soundness is close to the
definition of `Γ ⊢ c : A ! E`; it does not derive syntax-directed inference
constraints or prove the current solver implements the judgment. This
establishes a coherent *candidate typing rule* only for selected
`Value(A)` / `Susp(U,A)` boundaries with a known payload `A`. It does not prove
that Yulang3 annotation syntax selects the boundary, that row constraints
implement `E ⊆ U`, or that general Function subtyping, generalization,
instantiation, higher-order adapters, recursive definitions, and handlers
preserve the fragment. In particular, the Function-domain variance needed to
use this rule through a subtype or instantiated scheme is still open. The
proof is relative to the finite row abstraction and does not require exact
continuation-sensitive effect inference. These are candidate rules for review,
not a selected successor semantics.

An architect and independent compiler referee found two blocking omissions in
the first draft: the computation effect judgment ignored nonreturning request
prefixes, and the `suspend` rule left capture/allocation effects unconstrained.
The judgment now bounds every finite request-bearing prefix, with result typing
checked separately; `suspend` now requires `supp(Pref(capture(c))) ⊆ E_make`
and that capture does not evaluate the delayed body. Both reviewers confirmed
the repaired finite-prefix force argument under these explicit premises. They
also note that this trace-denotational fragment does not derive syntax-directed
inference constraints or settle function-domain variance. A specification
review confirmed the effect-row claims respect the syntax authority. The
architect's final delta review confirmed the capture-effect bound and
identified closure substitution as the remaining local proof bridge: the
stored body must retain its type/effect bound under the captured environment,
including nested latent facts. The fragment now states this assumption and
leaves its source proof open. A final compiler-referee and architect delta
review confirmed that the `c[ρ]` premise applies the force bound to the actual
stored body, while capture effects are separately bounded by `E_make`; the
conditional lemma is sound under its stated premises. Neither review proves
capture substitution for source lowering, mutable or opaque captures. No rule
has been selected or authorized for implementation.

#### Family support is a projection, not the effect constraint itself

A bounded architecture review examined whether the finite support domain must
encode operation payload and family type arguments directly. The smallest
candidate distinguishes the erased support head `FamHead` (a canonical family
constructor identity with type arguments omitted) from a typed family instance
`FamInst = (FamHead, type_arguments)`. The canonical resolver and the meaning of
family constructor identity remain unselected. It keeps

```text
support : TypedRequestEvidence -> P(FamHead) ∪ {TopEff}
```

as a support projection over request evidence only. A coupled typed-constraint/
evidence layer keeps the full `FamInst`, operation identity and signature,
payload/result constraints, and handler/grant eligibility. Typed annotations
and grants are checked against this full identity; equality after erasure to
`FamHead` cannot establish type matching or handler eligibility. Both layers
must be generated, solved, and transported together through generalization and
each independent instantiation. This is a representation candidate, not a
proof that the current finite-row solver can be composed with the typed layer.

For example, a request at `F<Int>.op` and a grant for `F<String>.op` both
project to support `{FHead}`. A rule that subtracts `FHead` using that
projection alone would erase a request that does not satisfy invariant
family-argument matching. The support projection may bound possible request
families, but it cannot type the payload, identify a covered operation, or
authorize `Drop`.
The typed matching constraints must remain meaningful source constraints, and
failed or unknown matching must retain the residual family. This schematic
conflict is not a claim about currently accepted Yulang3 syntax; the syntax
authority has not selected effect declaration or handler semantics.

#### Type refinement breaks the fixed-evidence monotonicity premise

The stability condition in the route-subtraction lemma is not a routine
property of a coupled type/effect solver. A typed-family witness shows why.
Let `α` be a type variable, let the only offer be `F<α>.op`, and let a handler
cover only the exact invariant instance `F<Int>.op`. Assume exact typed
matching, fixed non-type eligibility, no raw/unknown or other `FHead`
contributions, and a fixed arm support `A` with `FHead ∉ A`. Initially the
nonempty admissible type solution set contains both `α=Int` and `α=String`;
the family cannot be dropped for all assignments, so the projected support
retains `FHead`. Add the type constraint `α=Int`, with the refined solution set
still nonempty. All remaining offers match the handler, and the same support
family is now droppable. Thus constraint accumulation can shrink the combined
effect result even though erased `FamHead` support is unchanged.

Formally, if `Sol(C)` is the set of type substitutions satisfying `C`, the
universal drop test ranges over `Sol(C)`. For `C ⊆ C'`,
`Sol(C') ⊆ Sol(C)`, so a family that fails universal coverage under `C` may
pass it under `C'`. `Drop(C)` can grow as constraints accumulate;
consequently, the residual support can shrink. This is a counterexample to
support-inclusion monotonicity of the coupled transfer in the product order
where type constraints grow by inclusion and effect supports grow by
inclusion, with arm support fixed as above. It does not rule out monotonicity
under another refinement order or a different solution representation. The
preceding fixed-evidence lemma does not apply when evidence validity depends
on the admissible type solution set.

This is a schematic semantic counterexample, not a claim about a concrete
Yulang3 source form or a verdict that nonmonotone iteration is impossible. It
rules out only the unqualified claim that the type/effect operator is monotone
because its constraint store grows. Candidate routes still requiring proof
include a coupled solution relation over pairs `(type substitution, effect
bound)`, a proven phase order that freezes type matching before effect
subtraction, or a richer symbolic typed-row constraint that keeps the
match-dependent residual explicit. A phase order is valid only if effect
constraints cannot later refine the relevant types; otherwise it needs a
recomputation/fixed-point theorem. A typed-row relation must preserve
principality and final acceptance when projected to the chosen scheme
language. These are alternatives to investigate, not selected semantics or
implementation authority.

A scoped architect review confirmed the conditional counterexample and
required explicit premises: the refined solution set stays nonempty, there
are no additional/raw/unknown contributions of `FHead`, non-type eligibility
is fixed, and the arm support does not already contain `FHead`. The text now
states these conditions and limits the conclusion to support-inclusion
monotonicity in the stated product order. The review does not choose among the
candidate solver routes or establish a source construct for the schematic
family case.

#### Pointwise expressibility boundary for type-indexed handling

The same typed-family example tests what an ordinary, substitution-uniform
family row can express. Assume one request `F<α>.op` under a shallow handler
whose only exact invariant arm is `F<Int>.op`; the matching handler is
eligible, its arm/value path is pure and does not resume, and there are no
other contributions. In this typed exact-trace semantics, outward support is
empty when a use maps `α` to `Int`, and contains `F<String>` when it maps `α`
to `String`. The two uses have identical source row syntax before
substitution.

Suppose a generalized scheme can express only a fixed row template whose
membership is determined by its syntax and ordinary type substitution, with
no type-match predicate or delayed handler constraint. If the template omits
`F`, it is unsound for the `String` instance. If it includes `F<α>` (or just
`FHead`), it over-approximates the `Int` instance and can reject a pure use
that would be accepted by the pointwise semantics. Thus this row language has
no scheme that is pointwise least for both instances. The constant row
`{FHead}` can still be a sound principal result relative to a deliberately
coarser abstraction; the result here is a precision boundary, not a proof that
the coarse abstraction is non-principal. If final-acceptance compatibility
requires both pointwise outcomes, the generalized representation must retain
the type/handler correlation through a typed symbolic residual, per-use
re-elaboration, or an equivalent scheme relation. Merely delaying row solving
is insufficient only when generalization freezes a uniform row template and
discards that correlation; a later use phase that retains or reconstructs it
could recover the distinction.

This is an expressibility lemma under the stated source feature and scheme
language, not a claim that a concrete Yulang program has this shape or that
Oracle accepts either instance, or accepts the matching instance as pure. It
also does not show that the successor must use a negative type predicate
specifically: any equivalent correlated type/effect scheme can satisfy the
requirement. The capability audit therefore needs a frozen-Oracle fixture for
a type-indexed family request handled at one instance, with two independent
instantiations, and must separately check whether the matching instance is
accepted under a pure result bound and whether the nonmatching residual is
retained. Only if both outcomes belong to Oracle's supported final-acceptance
envelope does matching both become a compatibility requirement. No syntax or
implementation rule is selected here.

A scoped compiler-referee review initially found that this argument overstated
the need for a correlated scheme: the constant support row may be principal in
the deliberately coarse abstraction. The revision separates pointwise
expressibility from coarse principality and conditions compatibility on the
two Oracle outcomes. The closure review found no remaining issue in this
subsection; it does not characterize Oracle acceptance or authorize a richer
scheme language.

#### Oracle characterization limits the typed-instance premise

The pointwise witness above assumes that `F<Int>.op` and `F<String>.op` are
distinct exact handler identities. That premise is not established for
Yulang. Frozen Yulang2's adversarial-corpus contract for
`tests/yulang/yulang-adversarial-corpus/03_parameterized_effect_capture.yu`
explicitly says the same path `ask.get` at `int` and `str` must not be treated
as two operations; a collision must reject at execution rather than be hidden
by type-argument-based dispatch. Its effect documentation separately allows
parameterized families such as `ref_update 'a` and rows such as
`ref_update int`. A bug record states the intended expectation that
`[state int]` specializes the declared operation result type, but also records
that the probe failed and only conjectures which inference step is missing.
These observations point to a plausible split: operation/family path
determines handler identity, while family arguments constrain the operation's
type, rather than defining different operations. They are characterization
evidence, not a successor semantic rule.

The frozen implementation's `effect_family_matches_item` is an allow/filter
helper: it accepts a family path prefix and either empty family arguments or
matching argument arity, but does not compare argument values. This is
implementation evidence only and cannot establish dispatcher identity or
soundness. The precise source relation between a parameterized family
instance, operation signature, row annotation, and handler matching remains
to be proved. Therefore the `F<Int>`/`F<String>`
counterexample above only refutes support-inclusion monotonicity under the
conditional exact-instance matching semantics. It is not yet a valid Oracle
compatibility counterexample. The capability fixture must instead establish
the accepted behavior of one polymorphic operation path across independent
typed uses and handler specialization. As a successor proof obligation, keep
the meaningful type constraints without assuming that type arguments split
one operation identity; the source semantics must settle their relation.
No Oracle weight or runtime route is adopted by this correction.

A scoped architect review confirmed that the characterization limit is
accurate. It required distinguishing the bug record's expected behavior from
its observed failure, and describing the matcher as a path-prefix/arity helper
rather than exact dispatch identity. The revision closes those wording risks;
the source semantics itself remains open.

#### Frozen Oracle parameterized-family probes

To separate the documented same-path rule from the unverified typed-instance
example, I built a clean detached worktree at the frozen commit `a58eefc31`
and ran small `--no-prelude` source probes against its binary. The minimal
matching control was accepted and returned `100`:

```yu
pub act state 'a:
    pub get: () -> 'a

my run(action: [state int] 'r): 'r = catch action:
    state::get(), k -> k 100
    v -> v

run: state::get()
```

A second probe defined `answer_int` and `answer_bool`, each handling the same
`ask::get` path with a continuation value of its own type, then composed them
over one computation that performs `ask::get` at both `int` and `bool`. `check`
exited 0; execution rejected with `conflicting type candidates: int vs bool`.
This is consistent with the frozen corpus contract, but the probe alone does
not establish the dispatch mechanism. In frozen source commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1`, the effect-subtraction spec
requires same-path family arguments to constrain invariantly
(`spec/2026-05-31-effect-variable-subtractable.md`, lines 279–297), while the
runtime guard spec matches the exact operation path
(`spec/2026-06-13-runtime-guard-markers.md`, lines 83–92). Together these
support treating operation identity and family type constraints as separate
parts of the contract.

A third probe isolates the unsafe boundary. The handler formal says
`[ask int]` and resumes `ask::get` with an integer, while the supplied action
declares `[ask bool] bool` and the result is explicitly annotated `bool`:

```yu
pub act ask 'a:
    pub get: () -> 'a

my answer_int(action: [ask int] 'r): 'r = catch action:
    ask::get(), k -> k 1
    v -> v

my action(): [ask bool] bool = ask::get()
my result: bool = answer_int: action()
result
```

On the same clean frozen binary, `check --no-prelude` exited 0, and both
`run --no-prelude --no-cache --print-roots` and its `--interpreter` variant
exited 0 with `run roots [1]`. Frozen reference examples print Boolean roots
as `true`/`false`, so this result contradicts the declared `bool` contract.
This is a concrete unsound acceptance, although it does not yet isolate
whether the cause is row-family subtyping, handler specialization, or another
callback coercion path. The compatibility behavior to drop is accepting this
program and supplying an `int` through a continuation whose operation result
is declared `bool`. A sound successor must retain the type parameter
constraints from `ask.get` through the row contract and continuation, and
reject the incompatible callback/handler application before runtime; it must
not reclassify `ask int` and `ask bool` as distinct operation identities to
paper over the mismatch. The exact source typing rule remains subject to the
ordinary effect/handler design review. The frozen principal-monomorphization
spec also reconnects a generic operation's result type to the same family
item in the scrutinee row (`spec/2026-06-07-principal-monomorphization.md`,
lines 648–655), which gives a direct source-level constraint for that
continuation judgment.

The original larger adversarial-corpus fixture timed out at 30 seconds with no
output on the clean frozen binary, for both `check` and `run`; that exceeded the
corpus probe script's 20-second budget. This means its documented expectation
was not reproduced as a successful run. The three smaller probes above
completed quickly and supply the stated observations. This characterization
does not use `StackWeight` or the frozen dispatch helper as semantic authority.

This yields a concrete compatibility delta: the Oracle accepts a program
whose declared Boolean result becomes integer `1` in both execution engines.
The successor rejects that behavior on soundness grounds. The general
type-indexed residual expressibility witness remains conditional and must not
be conflated with this path-identity/type-consistency failure.

The scoped compiler-referee review confirmed that the third probe conflicts
with the declared operation type and that rejecting it is a justified
soundness-driven compatibility change. It also required the narrower wording
above: the mixed-use runtime conflict does not identify its dispatch cause.
This review closes the probe interpretation; the complete source typing rule
and its solver integration remain open.

#### Parameterized operation/continuation constraint extracted from the probe

A scoped compiler-referee derivation separates the constraints already
characterized by frozen specs from the successor rule still to be proved. Let
`p` be an exact operation path in family `F`, and let resolving its operation
scheme once produce a capture-avoiding substitution `θ`, payload type `Aθ`,
result type `Bθ`, and any declared latent effect constraints `Eθ`. The
candidate source-to-constraint interface must preserve all of the following:

```text
request at p:
  check payload against Aθ
  retain exact operation path p
  contribute typed family instance F<τ> to request/row evidence
  constrain the operation result to Bθ
  retain Eθ and its route/ownership obligations

handler arm at p:
  resolve the same operation path p and operation scheme
  specialize against the same typed family item F<τ> in the scrutinee row
  bind the payload pattern at Aθ
  bind continuation input at Bθ
  preserve the continuation's handler-result effect/value boundary
```

Whenever same-path family items meet in row splitting, duplicate collection,
subtraction, or handler eligibility, their type arguments must generate the
chosen invariant type constraints. A support-only projection may erase `τ`
only if those type constraints remain represented elsewhere. `F<Int>` and
`F<Bool>` do not become different operation identities: runtime identity stays
`p`, while the typed constraints determine whether the request and arm can be
related. This is the minimum candidate rule that rejects the minimized
counterexample: its request contributes `ask<bool>`, its arm requires
`ask<int>`, and the invariant relation cannot identify `bool` with `int`.

The clauses above are not yet an authoritative typing judgment. Frozen
characterization supports exact-path runtime matching, invariant constraints
for same-path family items in row operations, and reconnecting a generic
operation result to the same family item in the scrutinee row. It does not
settle source declaration lowering, binder ownership, handler grant/coverage,
callback subtyping, or the coupled least-solution proof. In particular, do not
drop `Eθ` merely because path `p` is handled: first determine which source
construct owns that effect and prove its handler routing. The old
monomorphization clause describes the continuation as
`Bθ -> shape(scrutinee_effect, scrutinee_value)`; the successor must decide
whether this shape is semantically required, then derive it from the chosen
handler judgment rather than importing it as authority.

The reviewer also recommends independently deriving the source-level
rejection of the probe under that successor judgment. The observed VM and
interpreter behavior establishes a compatibility conflict if reproduced; it
does not locate the missing constraint in the Oracle implementation. This
closes the narrow candidate-interface step, not the ordinary effect/handler
proof gate.

The source boundary needed by this candidate is therefore an elaboration
relation from source declarations/annotations and operation uses to canonical
family and operation identities, typed arguments/signatures, payload/result
constraints, support rows, and scoped handler/grant evidence. The syntax-v0
`EffectRowType` page supplies only direct `TypeExpression` CST items; it leaves
tail interpretation, row classification, and effect lowering undefined.
Current HIR retains generic expression values and treats the annotation tail
as an association barrier; it has no effect-row or operation-lowering object.
These are concrete missing bridges, not evidence for any particular source
rule. The existing Yulang2 `EffectFamily` argument behavior is characterization
only and cannot supply the successor's identity or matching semantics.

The next proof must establish that source elaboration preserves operation,
payload, and family-argument constraints; that SCC intrusion and independent
instantiation apply one capture-avoiding binder map consistently to request,
grant, and typed constraints; and that a family is dropped only when every
possible typed request offered to the handler is covered and eligible. Then
prove least solutions either for the coupled row/evidence domain or for a
staged analysis whose fixed eligibility evidence is already sound. The earlier
finite-lattice result applies only with `Drop` fixed and does not prove
monotonicity or principality for this coupling. No exact continuation-use
tracking is introduced: support may over-approximate traces, with principality
relative to the selected compositional abstraction. These obligations remain
open, and this representation has no implementation authority.

The exact-source delta review found no discrepancy with the syntax/HIR
authority. Compiler-referee review required an explicit distinction between
typed family instances and erased support heads; the text now defines
`FamHead`, `FamInst`, and a request-only support projection. A focused
compiler-referee closure review confirmed that this resolves the ambiguity and
that annotations/grants cannot use erased equality to authorize `Drop`. This
closes only the notation gap; source elaboration, coupled leastness, and all
semantic and implementation gates remain open.

#### Conditional typed source-to-constraint interface

An architect review recommends treating semantic lowering as the owner of the
typed evidence boundary, with the effect solver consuming its output and SCC
intrusion transporting it. This boundary can be specified conditionally before
choosing concrete source syntax. It does not yield an unconditional source
theorem because Yulang3 has not selected the operation, annotation, or handler
semantics.

For a fixed module and interface environment, a candidate elaboration judgment
returns four related products:

```text
Elab(Γ, source) = (TypeConstraints, RequestFacts, RowConstraints,
                   HandlerFacts)
```

- `TypeConstraints` retain operation signatures, payload/result types, and
  invariant family-argument obligations.
- `RequestFacts` are may-evidence for concrete or possible operation requests
  by typed `FamInst`, exact or unknown `OpId`, origin, and route/provenance.
  They include requests possible through calls, forces, continuation
  invocation, and imported or higher-order targets. Closed interface summaries
  may provide typed facts; an unbounded target adds an unknown fact.
- `RowConstraints` express annotation and call bounds. An annotation bound
  constrains a row but does not itself create a request origin.
- `HandlerFacts` retain operation coverage, typed grant obligations, and
  activation/scope provenance. They do not manufacture request facts either.

Only possible-request evidence contributes to support:

```text
support(RequestFacts) = case
  any fact has unknown family -> ⊤Eff
  otherwise -> { fam_head(q.family) | q is a possible request }
```

The support row may forget type arguments and route distinctions only because
the typed identities and route tags remain coupled to it. A call or force may
create a possible-request fact from a callable/thunk's latent contract; the
annotation supplying that contract does not itself claim a request origin.
Open or unbounded targets without a closed summary contribute unknown evidence
at every compatible handler. Every concrete request-bearing execution step
must be covered by a possible-request fact, or by a sound symbolic summary
that covers it.

For a proposed `Drop` at handler `H`, every possible current or forwarded offer
of family `f` must be covered by the exact operation and eligible at that
activation. A `RawOnly` fact is not an offer to `H`; instead its effect must be
preserved in the matched continuation's latent `E` and charged to the arm or
captured result that invokes or exports it. A mixed route must satisfy both
conditions. Any unknown or unclassified route blocks `Drop`. These remain the
offer/RawOnly/Unknown obligations from the preceding route lemma; this source
interface alone does not establish them.

For a source derivation that owns one static type binder `α` across request,
annotation, payload, and grant evidence, each independent use must apply one
capture-avoiding map `θᵢ` to every type occurrence owned by `α` in the
corresponding fields of all four products.
The same rule applies to each SCC parent/use map. Preserved outer identities
use the shared anchor map; internal SCC uses remain live. Hygiene/handler
binder transport is a separate map, and dynamic activation identity is
generated by evaluation rather than identified with a compile-time binder.
Maps may be split only when the source binder ownership proof says the
identities are independent. This preserves the distinction between shared
type identity, static handler evidence, and dynamic scope.

The need for a common type map has a small counterexample. Suppose one
generalized source component gives the same binder `α` to a request at
`F<α>.op` and its typed grant. Correct instantiation maps both to `F<β>.op`
and `F<β>`. If request and grant are independently freshened to `F<β>.op` and
`F<γ>`, the solver may choose `β = Int` and `γ = String`. Their `FamHead`
projections still agree, but the source-shared type identity has been lost.
Full typed matching must then withhold `Drop`; this can add a residual effect
and reject a program that the shared-binder derivation admits. If matching
instead uses only `FamHead`, subtraction is unsound. The example demonstrates
why preserving the relation is needed for soundness and acceptance, not a claim
that independent freshening alone always causes unsoundness. It is schematic,
not a claim about currently accepted Yulang3 syntax.

The conditional transport obligations are:

1. elaboration emits possible-request evidence for every concrete request-
   bearing step, including calls, forces, forwarded suffixes, and higher-order
   targets; it uses unknown/top when no sound target summary exists, while
   annotation bounds and handler coverage never fabricate origins;
2. a common capture-avoiding renaming commutes with operation/family type
   constraint generation and preserves `fam_head` support;
3. each use-site map is common across request, annotation, payload/result, and
   grant occurrences for every source-shared binder, while independent uses
   remain disjoint and outer anchors remain shared;
4. a `Drop` certificate covers every possible current/forwarded offer under
   every admissible typed solution and represented dynamic activation, while
   preserving `RawOnly` effects through continuation latent bounds and
   arm/result summaries; forwarded re-entry and mixed routes remain included.

Items 1–3 can be proved as elaboration and transport lemmas once the source
interface defines binder ownership and typed family matching. Item 4 depends
on the route/provenance quotient and handler semantics. If eligibility is
computed before type solving, it must be conservative for every admissible
assignment; if it is refined after solving or jointly with rows, the combined
analysis needs a monotonicity/leastness proof. The current finite-lattice
theorem covers neither source elaboration nor the coupling. Exact
continuation-sensitive precision remains unnecessary; sound over-approximation
and principality relative to the selected abstraction remain the targets.
These are conditional proof obligations, not selected Yulang3 rules or
implementation authority.

#### Typed-evidence alpha-transport lemma (conditional)

Fix a well-formed candidate elaboration result
`E = (C, Q, R, H)` from the interface above under a fixed type environment
`Γ`. Let `θ` be a bijective, capture-avoiding renaming of local/generalized
type variables in `C`, typed requests `Q`, row constraints `R`, and typed
grants in `H`. It fixes every free outer/interface variable in `Γ`, and leaves
`FamHead`, `OpId`, source origins, and route tags fixed. Let `Trθ(E)` apply
that same map to every type position in all four products.

Then the following structural transport facts hold, provided the selected
family-match predicate is defined from `FamHead`, `OpId`, and ordinary type
constraints that are themselves equivariant under `θ`:

1. `support(Trθ(Q)) = support(Q)`, because `fam_head` erases only type
   arguments and `θ` does not rename the canonical family constructor;
2. each generated payload, result, and invariant family-argument constraint
   maps to its corresponding renamed constraint;
3. every typed request/grant match under a type assignment corresponds to the
   match under the alpha-renamed assignment, and the converse holds for the
   inverse renaming; and
4. the type-constraint solution sets
   `Sol_type(Γ,C) = {ν | ν satisfies Γ and C}` and
   `Sol_type(Γ,Trθ(C))` are alpha-equivalent, by the bijection that renames
   assignments to local/generalized variables along `θ` and fixes `Γ`.

This fourth claim is only about the stated type-constraint relation. It does
not transport row/effect solution sets: that would additionally require every
row transfer, fixed `Drop`, interface filter, and callback input to commute
with `θ`, premises not established here.

The typed-match part of a `Drop` certificate is alpha-invariant under the same
assignment bijection. Full certificate invariance additionally assumes an
evaluation/observation correspondence between the two elaborations that gives
a bijection on reachable request/handler configurations and preserves current
and forwarded offers, `RawOnly`/mixed/unknown route classes, operation-arm
coverage, and per-activation eligibility. It must also preserve and reflect
the row-side certificate: the matched continuation's latent `E`, and every
arm/result/callback row obligation that charges `E` when the continuation is
invoked or exported. This is a local evidence-transport premise; it does not
claim equivariance of the whole row solver or its solution set. If compile-time
hygiene identities participate in the correspondence, `Θ` must map their
ordered boundary lineage and scope evidence. Dynamic activation identities
are related by this assumed correspondence; they are not renamed as
compile-time IDs. The correspondence itself is unproved, so no unconditional
full-`Drop` invariance follows.

The proof is structural: `θ` fixes family and operation constructors, fixes
outer variables, maps each local type-bearing constraint homomorphically, and
is bijective. Typed matching and type-constraint satisfaction are therefore
preserved and reflected for corresponding assignments; the same bijection
transports the universal quantifier over those type solutions. Route tags and
ordered provenance labels are unchanged, but this alone does not relate their
reachable dynamic configurations. This proves a conditional alpha-transport
property for support, typed constraints, and type solutions, not source
elaboration soundness, full `Drop` invariance, row-solver principality, or
Oracle-equivalent acceptance.

#### Scoped member-view factorization for SCC use maps (conditional)

The preceding alpha lemma takes one map that fixes its receiver environment.
The candidate graph-boundary operation instead has a per-member/per-use map:
`Gen_d ∪ Cycle_d` goes through `Phi_d` and `sigma_(d,u)`, while `Free_d`
resolves through the component-stable anchor map `beta_C`. A raw source ID
therefore cannot necessarily be renamed by one global map across all member
views.

For a prepared member view `H_d`, the existing `V_d` partition covers only
identities occurring in `H_d`. The typed interface also carries identities in
`C/Q/R/H` and in selected evidence. Define the full interpreted identity
support of the member view as

```text
IdView_d = VarIds(H_d, root_d, selected_edges_d, recursive_bounds_d,
                  C_d, Q_d, R_d, Hfacts_d)
           ∪ ⋃ Supp_d(e) for mapped evidence items e
```

Here `VarIds` includes every type-variable occurrence in each listed product;
`Supp_d(e)` is the graph draft's transitive evidence payload/proof/validation
support. For a mapped-evidence route, require a complete disjoint partition
`IdView_d = LocalView_d ⊎ FreeView_d`, extending
`Gen_d ∪ Cycle_d ⊆ LocalView_d` and `Free_d ⊆ FreeView_d`. `Gen_d ∩ Cycle_d`
is allowed and remains one identity. Every ID must be classified once per
member view; any ID that cannot be classified rejects the candidate transition
before publication. An `Erase_d` ID must be absent from `IdView_d` and unread by
all four products and their evidence. A pinned-evidence route is not inserted
into `Supp_d` for type renaming: its proof snapshot remains opaque and must
remain valid by the separate pinned-evidence condition. Other non-type proof
IDs and validation dependencies use their evidence-specific map, such as
`Xi_d`, with validity preserved or rechecked; they are never silently treated
as type-variable IDs.

Extend `Phi_d` injectively to a member-view port map on **all** of
`LocalView_d`, and extend `beta_C` injectively to all of `FreeView_d`, retaining
the same receiver anchor for each preserved identity. First form a
member-scoped view by rebasing **every occurrence** in the root, selected
edges, recursive bounds, `C/Q/R/H` products, and mapped identity-bearing
evidence:

```text
B_d(v) = Port_d(v)       if v ∈ LocalView_d
       = beta_C(v)        if v ∈ FreeView_d
```

Here `Port_d` is the member-owned image of the extended `Phi_d`; its namespace
is disjoint from the shared anchors and receiver identities. `beta_C` maps
`FreeView_d` to those shared anchors.

For one external use `u`, define one map on the rebased view:

```text
theta_(d,u)(Port_d(v)) = sigma_(d,u)(Port_d(v))
theta_(d,u)(a)         = a                         for receiver anchor a
```

To invoke the preceding alpha lemma, assume the rebased four-product view is
well-formed under a fixed `Γ` containing these receiver anchors, and that its
family-match predicate and type-constraint rules commute with this renaming.
Those source/interface premises are not established by the graph map itself.

Require extended `Phi_d` to be injective on `LocalView_d`, `beta_C` to be
injective on `FreeView_d` with an image disjoint from the member ports,
`sigma_(d,u)` to be injective on `Port_d(LocalView_d)`, and the composed map

```text
rho_(d,u)(v) = sigma_(d,u)(Phi_d(v))   if v ∈ LocalView_d
             = beta_C(v)               if v ∈ FreeView_d
```

to be injective on all of `IdView_d`. The use's fresh range avoids the full
`I_recv`, every member port domain, and all other use ranges. The map is applied
consistently to all four elaboration products, roots, both edge directions,
recursive-bound payloads, and their validity evidence. Because
the local port domain is disjoint from the fixed receiver environment, this
finite injective map can be extended to a capture-avoiding permutation of the
type-identity namespace, under the candidate assumption that the namespace
has an infinite fresh supply. The typed alpha-transport lemma then gives
support invariance, typed-constraint transport, and alpha-equivalent type
solutions for this one member view. It gives no row/effect solution theorem or
dynamic `Drop` result.

For distinct external uses of the same member, require disjoint local fresh
ranges while keeping the same receiver anchors fixed. Thus a source-shared
identity within one member/use has one image, independent uses do not alias,
and imported/non-generic anchors remain shared. Internal SCC uses bypass this
freshening map and continue to reference the open live root by identity; they
are not instances of the external-use alpha theorem. `Theta` continues to
transport hygiene binders separately from type identities.

A cross-member witness shows why the rebase cannot be omitted. Let raw type ID
`x` be local in one saved view `H_a` but free in another `H_b`, with
`beta_C(x) = x`. An external use of `a` maps its occurrence of `x` to a fresh
identity, while `H_b` must preserve `x` as the receiver anchor. No single
global map on the raw ID can do both. The scoped `B_a`/`B_b` maps distinguish
the two ownership roles before use freshening. This is only a map-shape
counterexample: the source partition and cross-member root/use relation still
need proof.

This factorization is conditional on complete classification of `IdView_d`,
injectivity, evidence closure/validity, freshness, and the common type-binder
ownership relation across each view's `C/Q/R/H`. In particular, a type
variable appearing only in `C/Q/R/H` still receives a local port or shared
anchor and cannot be left at its raw ID. It does not prove that Oracle
root projection constructs such views, that member maps compose in a joint
cross-member continuation, that handler activation observations correspond,
or that the full source/effect solution is principal. A collision or an
identity that must be both fixed and fresh inside one rebased view invalidates
this corollary and must reject the candidate transition unless a separate
quotient/ownership proof resolves it.

#### Joint member/use transport criterion (conditional)

The per-view alpha result does not by itself justify taking a union of
independently rebased member views. For each external use `j=(d,u)`, let
`C_j` and `root_j` be that member's complete selected constraint view and root;
all internal SCC edges and recursive-bound links selected for that view stay
inside `C_j`. Also include `C_base`, the complete base/group-validity view.
For every copy `j∈J={base}⊎Uses(e)`, let `L_j` be its local identities after
rebasing; for external uses, `root_j` is the observed member root. Let
`A_shared` be the receiver anchors. Independent copies have
disjoint `L_j`, even when their saved views contain the same raw TypeVar ID.
Let `A_fixed` contain every identity fixed in the receiving context: receiver
anchors, caller/continuation identities, and any other free identity observed
by a copied root or constraint. `A_shared ⊆ A_fixed`. Every occurrence in a
copied constraint, evidence item, and root observation must have exactly one
owner: either a fixed identity in `A_fixed`, or a tagged local `(j,v)` for one
copy. Raw IDs alone do not assign ownership. The batch source and target
identity spaces are

```text
I_src = A_fixed ⊎ ⊔_(j∈J) L_j
I_dst = A_fixed ⊎ ⊔_(j∈J) rho_j(L_j)
rho(a) = a                              for a ∈ A_fixed
rho(j,v) = rho_j(v)                     for v ∈ L_j
```

Here each `C_j` for `j∈Uses(e)` is the complete selected member view, including its
internal SCC and recursive-bound edges. Their local namespaces are disjoint
even when source views reuse a raw ID. Each `rho_j` consistently transports
every occurrence in its copy, including roots, recursive-bound payloads, and
mapped evidence. It is injective on `L_j`; its image avoids all of `A_fixed`
and every other fresh image. The batch relation also contains
receiver/continuation constraints `K_ctx` that connect one or more copied roots
to fixed caller variables or to each other. Each occurrence in `K_ctx`, its
type-bearing evidence, and every root observation must use the same unique
fixed-or-tagged-local ownership classification. Non-type proof IDs use their
evidence-specific map and their validity must be preserved or rechecked. No
additional
cross-use equality is implied solely by coincident raw IDs in two saved
member views. If the declarative source-use rule does require such a link, it
must be present in `K_ctx` or represented by one shared identity before the
fresh ranges are allocated.

Thus `rho` is a bijection from `I_src` to `I_dst`, fixing `A_fixed` and mapping
each tagged local copy to its fresh namespace. Assume the selected
type-constraint predicates and family matches commute
with this capture-avoiding renaming, as required by the preceding typed
alpha-transport lemma. Then the assignment map from the original batch domain
to `I_dst` is a bijection. By structural evaluation of endpoint expressions
and the assumed predicate equivariance, every obligation in each copied view,
every `K_ctx`
obligation, and every root observation has the same truth/value under
corresponding assignments. The inverse map gives reflection. Hence the
complete batch solution relation, including an empty fiber, is preserved.
This argument allows `K_ctx` to couple distinct uses; it does not factor the
solution relation into independent use fibers unless `K_ctx` only references
fixed shared anchors.
This is a type-identity transport claim only. Effect-row/evidence maps,
hygiene binders, and dynamic handler observations need their own transport
relations; no weighted-constraint or row-solver solution theorem follows.

This corrects an ambiguity in the first wording of the criterion: internal
live-root and recursive edges are transported within each `C_j`, not treated
as identity links between separate external use copies. For example, if raw
ID `x` is local in saved view `H_a` and free in `H_b`, a use of `a` maps its
copy of `x` to a fresh local while a use of `b` resolves its occurrence to
the receiver anchor. That is valid when the two external scheme uses are
independent under the declarative rule. If some source constraint or
monomorphic use context requires these occurrences to denote one value, the
constraint must be carried in `K_ctx`; omitting it can change the joint
solution set. The raw ID alone decides neither case.

A minimal constraint-graph instance separates these cases. Let
`C={a≤x, x≤b}` with distinct anchors `a,b,x₀`; consider a root view `H_A`
whose root is `x` and whose `x` is local, and a view `H_B` whose root is the
same saved source ID `x` but whose `x` is free through shared anchor `x₀`. Under
external uses `u_A,u_B`, the two copies become

```text
C_A = { a≤x_A, x_A≤b }      root_A = x_A
C_B = { a≤x₀, x₀≤b }        root_B = x₀
```

Here `x_A` is fresh and independent of `x₀`; that is exactly the two views'
declared ownership. A continuation constraint `root_A≤root_B` belongs to
`K_ctx` and becomes `x_A≤x₀`. Every satisfying pair transports in both
directions by assigning the old local `x` the value of `x_A` and leaving
`x₀,a,b` fixed. If the intended source relation instead says that `x_A` and
`x₀` denote one shared value, the graph above is incomplete without an
explicit equality/link; the transport argument does not invent one. This
example validates only the map algebra after the two partitions are supplied.

The criterion is conditional on complete member views, correct source binder
ownership, and a complete `K_ctx`. It does not prove that the Oracle's ordered
root projections or the successor's source elaboration construct those
objects. In particular, the same original SCC edge may be copied into each
external scheme use while its local identities are freshened independently;
the proof must preserve that per-use copy semantics rather than force
cross-use sharing.

#### Instantiation in the reviewed uniform pure-SCC subcase

For the conditional pure recursive-group-plus-nested-let theorem in
`2026-09-30-intrusion-parent-transport-composition.md`, every SCC-created
identity is local in the base and each member-use view, and every referenced
outer identity is fixed. Thus the base copy and each use copy contribute one
disjoint local namespace, while the same `A_J ∪ K` is fixed. Its joint map
`Λ` transports the base graph, every member-use copy, caller-root constraints, and cross-use
constraints in one assignment relation. This supplies an explicit `K_ctx` and
satisfies the criterion above for that already reviewed pure fragment; in
particular, the root selected from a group copy does not create a different
identity partition.

This is only a consistency corollary of the reviewed conditional theorem. It
does not establish any mixed `Local_d`/`Free_d` case: the pure fragment has no
member-specific fetch boundary, effects, or post-boundary mutation. Applying
the criterion to the Oracle's ordered root projections still requires the
source-derived per-view ownership classes and every root/use bridge.

An architect review recommended this conditional semantic-lowering boundary;
the exact-source review found no conflict with syntax-v0 or current HIR. The
compiler-referee review then found three gaps: possible calls/forces were not
represented as request evidence, `RawOnly` was incorrectly quantified as an
offer, and split-freshening was described as unsound without the needed faulty
`Drop` premise. The candidate now adds may-request evidence and unknown/top
fallback for unbounded targets, separates offer coverage from raw-continuation
preservation, and limits the counterexample to lost identity and possible
acceptance loss (with unsoundness only if erased-head matching is used). A
focused compiler-referee closure review confirmed all findings are closed.
Source elaboration, route completeness, finite activation abstraction, and
coupled leastness remain unproved.

The compiler-referee review of the alpha-transport lemma found two major
scope gaps: the initial solution-set claim included row/effect behavior under
an untransported interface, and the initial `Drop` claim inferred dynamic
configuration correspondence from static binder transport. The revision fixes
outer/interface variables, limits the solution claim to `Sol_type(Γ,C)`, and
makes full `Drop` invariance conditional on an explicit evaluation/observation
bijection. A follow-up review found that this premise also needed to preserve
the `RawOnly` latent-`E` and arm/result/callback row obligations; those are now
included while whole row-solver equivariance remains excluded. A fresh
compiler-referee closure review found no remaining issue in this delta. The
required dynamic correspondence and all source/effect solver theorems remain
unproved.

## 2026-10-02: source-level counterexample to unconditional parent merging

A source witness has now been characterized against a clean build of frozen
commit `a58eefc31e22141574b6f20c6a5748151c6d79f1`. The fixture
`/tmp/yulang-intrusion-source-scc-independent-parents.yu` defines mutually
recursive `f` and `g`; each accepts two callbacks with independently typed
`pulse` effects, and recursive references occur in a statically unchosen
branch so the executed branch returns unit. `spin()` supplies bottom-typed
callbacks in those branches without equating the members' parameters. Frozen
Oracle `check --no-prelude --no-cache` succeeds, raw scheme output assigns
`f` distinct quantified identities `'23` and `'28` and `g` distinct
identities `'53` and `'66`, and `run --interpreter --print-roots` succeeds.
The two external calls instantiate `f`'s callbacks at `int,bool` and `g`'s
at `bool,int`. This is source-level evidence that unconditional parent
identification loses accepted uses. It does not prove that any particular
successor quotient is principal. The exact quotient criterion remains
observational, and the positive theorem for identities entailed equal by the
complete source relation remains open. The binary came from an isolated clean
archive; no test suite or compiler implementation was run.

The draft's positive direction is a conditional whole-formula quotient lemma:
if the complete relation entails pointwise equivalence within each proposed
parent fiber, and formulas/observations respect that equivalence, substitution
through the whole presentation preserves its solution fiber. This closes the
abstract algebraic implication, not its source premise. Source typing must
still prove that candidate parent fibers satisfy the entailment, including
every root and typed-family observation; the exact necessary-and-sufficient
observation criterion remains impractical until that observation is fixed.

Reproduction commands from the archive root were:

```sh
cargo build -p yulang
target/debug/yulang --no-prelude --no-cache check /tmp/yulang-intrusion-source-scc-independent-parents.yu
target/debug/yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-source-scc-independent-parents.yu --poly-raw
target/debug/yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-source-scc-independent-parents.yu
```

The exact frozen source tree was materialized from the archive of
`a58eefc31e22141574b6f20c6a5748151c6d79f1`; the raw dump showed the root
quantifier identities listed above. This is a focused oracle characterization,
not a Rust test-suite run.

The SCC-use-map architect review found that a raw type ID can be local in one
member view and free in another, so the per-use renaming cannot be treated as
one global map. The candidate now factors each member view through a complete
`IdView_d` classification, a local port rebase, and then the external-use map;
the counterexample is limited to map shape and does not claim a source-level
failure. Compiler-referee review required the full support partition and fixed
`Γ`/equivariance premises before applying the typed alpha lemma. Those gaps
were repaired. Its closure review then caught a map-domain wording error; the
current condition states injectivity separately on `LocalView_d`,
`FreeView_d`, and `Port_d(LocalView_d)`, and requires the composed `rho_(d,u)`
to be injective on `IdView_d`. The scoped factorization remains conditional:
source ownership, cross-member composition, handler observations, and
effect-solution principality are still open.

A primary adversarial reread found that the first joint-use criterion
conflated internal SCC edges in a saved graph view with identity links between
separate external scheme uses. The criterion now transports each complete
member-view copy under its own local map and reserves `K_ctx` for actual
receiver/continuation constraints coupling those copies. Repeated raw TypeVar
IDs across independent uses do not imply shared assignments; a source-required
link must be explicit. This correction is primary-reviewed only. The exact
mixed `Local_d`/`Free_d` source ownership relation and completeness of
`K_ctx` remain open.

The primary proof audit tightened the stated map theorem further: selected
type-constraint and family-match predicates must satisfy the equivariance
premise of the preceding alpha lemma, and non-type proof IDs need their
evidence-specific transport/validity condition. Weighted rows, effect
solutions, hygiene transport, and dynamic handler observations are explicitly
outside this batch result. No independent review has yet been run on the
corrected criterion or its two-view example.

#### Source-rule audit: operation typing and handler reconnection

A read-only architecture audit checked the active successor candidates against
the current syntax reference and the frozen Oracle specification/source. The
current Yulang3 syntax reference defines effect-row and catch syntax but does
not specify their typing or visibility semantics. The frozen material is
characterization evidence only: it documents exact operation-path dispatch,
invariant constraints on same-path family arguments when rows meet, operation
payload/result reconnection through a common signature-variable map, and the
shallow rule where a matching arm receives the raw continuation while a
forwarded request retains the handler around its suffix. None of those Oracle
weight or runtime-marker rules is adopted as successor authority.

The smallest source-elaboration obligation is now explicit: produce typed
request and handler facts carrying exact `OpId`, typed family arguments,
payload/result types, and all declared latent effects; reconnect request, arm,
and continuation through one capture-avoiding binder map; then define
per-stage callback receipt, residual-closure capture, invocation/force, and
visibility against a fresh live handler activation. The finite-trace transfer
may conservatively retain support, as directed; exact continuation-sensitive
inference is not required. A `Drop` certificate must cover every possible
typed current or forwarded offer. Principality still needs a leastness proof
for the coupled row/evidence abstraction (or a justified phase-separated
construction).

The frozen `ask<bool>` action accepted under an `ask<int>` handler and returned
as an integer remains a concrete soundness conflict. The successor should
reject this typed mismatch; the precise Oracle dispatch defect remains
unisolated. This records an acceptance delta without treating the Oracle's
path-only matching or weight propagation as semantics.

Audit scope: `syntax-reference/en/src/types/effect-row-type.md`,
`syntax-reference/en/src/expressions/case-catch.md`, the candidate source and
operation/continuation sections above, and frozen commit `a58eefc31` effect and
runtime-guard specifications plus relevant inference lowering. This is a
conditional proof handoff, not a selected rule, authority change, or
implementation gate. The callback contract's grant meaning and lifetime,
operation-latent-effect ownership, open-row denotation, coupled leastness, and
full source-to-trace simulation remain unresolved.

#### Typed shallow core judgment (candidate)

To turn that handoff into a proof target, use a computation judgment that
retains the type/effect distinction and occurrence evidence:

```text
Γ ⊢ e ⇓ (τ, E, Q, K_sym)

τ       result type, including latent effects/request facts in any
        Function/suspension types
E       abstract support bound for request-bearing finite prefixes
Q       may-request facts, each retaining typed family instance, exact or
        unknown OpId, payload/result types, origin, ordered lineage, and route
        class (scrutinee offer, raw suffix, or arm request)
K_sym   symbolic type constraints/evidence, including invariant family-argument
        obligations linked to their request and row occurrences
```

The `E` component is only a projection: it may forget family arguments and
routes because `Q` remains coupled to it. An annotation or handler coverage
declaration constrains types/rows; it does not itself add a request to `Q`.
Unknown call/force targets contribute an unknown request fact and `TopEff`.
The abstraction is deliberately conservative and does not count continuation
uses.

Resolve an operation declaration once per source use under one
capture-avoiding substitution `θ`. The resolved operation signature contains
`Aθ`, `Bθ`, and every declared effect obligation `Λθ`. Its ownership is an
explicit parameter of this candidate: each obligation must be assigned to the
request itself, a returned Function/suspension, an adapter, or another named
evaluation point by source semantics. It is never discarded. If the owner is
unknown, retain the typed obligation and widen its possible request support to
`TopEff` at every possible owner; do not guess that it is immediate or latent.
This includes both the current request/call and every returned
Function/suspension or adapter that may carry the obligation. Such values
retain an `Unknown` latent request fact and `TopEff` latent bound through
capture, escape, generalization, fresh instantiation, and intrusion; a later
call/force charges that latent bound to its own immediate effect. For
`op : A -> B` in
exact operation path `p` and family instance `F<ᾱ>`, the request contribution
is:

```text
q = (F<θ(ᾱ)>, p, payload : Aθ, result : Bθ, Λθ, origin, lineage)
E_call = {head(F)} ∪ support(immediate-owned obligations in Λθ)
          ∪ (TopEff if any Λθ owner is unknown, otherwise ∅)
```

Every unknown-owned obligation contributes an `Unknown` request fact at each
possible owner in `Q`; `TopEff` is not a replacement for retaining the typed
`Λθ` payload. Obligations classified as latent remain attached to their owning
Function/suspension type and contribute when that value is called or forced.
This keeps the equation sound while the source semantics for ownership is
unresolved, at the cost of conservatively widening both immediate and latent
bounds wherever ownership may lie.

Sequential composition unions `E_call` and the continuation/body support.
Payload and result types retain their complete nested Function and suspension
latent rows; family arguments remain in `q` and in ordinary type constraints.
When a row operation relates two instances with the same family head, it
generates invariant argument constraints in `K_sym` before modifying either
row. The family head is not a substitute for those constraints, and distinct
operations at one family remain distinct `OpId`s.

For a shallow catch, let the scrutinee have result `S`, support `E`, and facts
`Q`; let its value and operation arms return `R`. An exact-path request for
`p : ∀b̄. A -> [Eop] B` is resolved under request map `θ`; the matching arm
resolves the same declaration independently under map `φ`. The arm receives
payload `Aφ` and raw continuation `k : Bφ -> S ! E`. Its constraints include
the request/arm signature-coherence obligations
`Aθ <: Aφ` and `Bφ <: Bθ`, plus the separate invariant family relation.
The continuation returns the scrutinee's result `S`; typing the arm's whole
body at `R` is a separate obligation. This whole-`E`
latent bound is conservative: every finite suffix after the request is
included in the scrutinee's finite-prefix bound. The arm's ordinary
application judgment charges `E` whenever it calls `k`; its latent request
facts are transported with it. Returning a closure that captures `k` must
retain both the latent bound and those facts on the closure. The matching
catch is not reinstalled around raw `k`.

Let `Offered(Q,H)` include only scrutinee-side request facts that can be
presented to this activation, including forwarded suffixes after outer
resumption. It excludes raw suffixes run outside this shallow handler and
requests produced by this handler's own arms. If one summary contribution can
take both an offered and raw/arm route, retain both tagged facts. Define
`Drop_H` only from proof certificates that every possible offered fact of each
dropped family is (1) a typed instance of an exactly covered operation, (2)
visible to this activation under its occurrence-local lineage, and (3)
actually offered to this activation. Unknown identity, type, lineage,
activation, or route classification blocks the certificate. The candidate
effect result is:

```text
E_catch = (E \ Drop_H) ∪ A_value ∪ ⋃ A_operation
```

where each arm support is derived with its continuation typed at `E`. The
union intentionally keeps an effect reached after a shallow resumption, even
when the initial request is handled. It also conservatively keeps arm effects
for clauses that may be unreachable; no exact continuation/branch correlation
is claimed. For the candidate open-world abstraction, `TopEff \ Drop_H` is
defined as `TopEff`; finite subtraction from unknown support cannot justify a
drop.

The judgment is compositional only if its request-fact component is as well as
its row component. For this candidate, raw continuation types carry the
scrutinee suffix facts `Q_suffix`; ordinary call/force adds the callee's
latent facts at that evaluation point; closure construction preserves captured
facts; and arms derive `Q_value` / `Q_operation` under those rules. The catch
transfer is therefore:

```text
Q_catch = Forwarded_H(Q_scrutinee, Drop_H)
          ∪ Q_value
          ∪ Q_operation
```

`Forwarded_H` preserves each remaining occurrence and its typed identity,
adds the forwarding/re-entry boundary events, and retains its suffix facts.
Arm facts keep an arm origin and are outside this handler's offer set, though
an outer handler may see them. The transfer must map unresolved route or
ownership information to `Unknown`/`TopEff`. It may not delete a fact merely
because its family head appears in `Drop_H`. This definition states the
required compositional interface; source rules for producing these facts and
the boundary-event updates are still unproved.

`K_sym` follows each request/row fact through this transfer. Before a head is
removed or moved by split, subtraction, matching, or residualization, any
same-head invariant argument relation is emitted into `K_sym` and attached to
the resulting evidence. Constraint solving maps its endpoints through the
current substitution and retains the relation until a solver proof explicitly
discharges it. Generalization closes over the obligation endpoints; fresh
instantiation applies the same binder map to the row facts and `K_sym`; and
intrusion applies the type-parent map to both endpoints and evidence payloads.
A discharged relation remains represented by its proof/equivalence evidence
where later row transport needs it. No phase may defer generating or
reconstructing `InvArgs` until concrete family rows are materialized.

#### Conditional finite-prefix soundness claim

Assume source evaluation has the free resumable-tree behavior from the shallow
trace calculus; every concrete request step is represented in the
compositional `Q` transfer above; every declared operation effect obligation
`Λθ` is charged at its true owner (or conservatively widened if unknown); `E`
contains the support of every finite request-bearing prefix; exact typed
coverage and `Visible` soundly predict the selected live handler; and each
arm's ordinary typing is sound when raw `k` has latent support `E`. Then every
finite prefix of the caught computation is bounded by `E_catch`.

Proof sketch: an uncovered, invisible, unknown, or unoffered request remains
in `E \ Drop_H`; a covered visible offered request is consumed at its first
matching activation, so its operation arm is bounded by its arm judgment. If
the arm calls raw `k`, the called suffix is bounded by `E` and therefore is
charged in the arm support. If an unmatched request is forwarded and an outer
handler resumes it, the wrapped suffix remains among `Offered`; the universal
certificate cannot drop a family if that suffix can later escape. Any finite
trace has finitely many such steps, so induction on its prefix length gives
the bound. This proof uses no weight routing and no continuation-use count.

This theorem is still conditional: it assumes the operation elaborator, typed
visibility relation, arm judgments, and `Drop` certificates whose construction
is the actual open problem. The rule also does not yet establish principality.
To prove leastness, the request/route abstraction and row constraints must be
shown jointly least for its concretization; the fixed-`Drop` finite-lattice
lemma alone is insufficient if type refinement or stage evidence changes
coverage. Treating this as an implementable rule before that coupled proof and
independent semantic review would violate the design gate.

#### Unified typed-row algebra (preferred direction, semantics open)

The newest user direction rejects turning the source-site checklist below into
a family of semantic selectors. The checklist is characterization/proof
bookkeeping only. Prefer one typed-row algebra from which the familiar cases
follow:

```text
TypedRow       finite family-instance representation with a denotation
RowDen         possible typed requests represented by a TypedRow
RowIncl        subset of RowDen, the may-effect upper-bound relation
RowUnion       denotational union of may-effect rows
FamAgree       one common-witness relation for source-derived shared slots
RowRemove      support removal justified by complete handler coverage
```

Under this candidate, filters and callback effect bounds invoke `RowIncl`;
row splitting follows from inclusion over `RowUnion`; handler subtraction is
`RowRemove` justified by complete typed coverage and route evidence. Typed
argument agreement is separate: `FamAgree` applies only to occurrence groups
that source semantics says share one family argument. These are general
relations, not source-site selectors. A source rule determines the operands
and any shared-slot grouping; it does not invent a new argument comparison at
each site. Frozen weight routing cannot decide those premises.

`Sel_s` can remain as proof notation for the pairs exposed by evaluating
these general relations, not as a core semantic object. Likewise, `Demand` is
not a source construct: mathematically it is the dependency of an observed
root/request/residual on a relational premise; an implementation may store
those dependencies as graph edges or proof references. The operation's
relation and its symbolic formulas remain in the semantic constraint graph.
The maps for type endpoints, row occurrences/owners, and handler identities
remain distinct components of one labeled graph morphism because they act on
different identities, but transport is one compositional operation checked
against one denotation-preservation theorem. Runtime route/visibility evidence
stays separate from typed-row compatibility because it expresses a genuinely
different fact: whether a concrete offered request is handled at an
activation.

This is a conceptual comparison, not a selected design. A source-indexed
selector system is precise about each trigger but creates one semantic proof
obligation per site and risks mirroring Oracle internals. A typed-row
semilattice offers more proof reuse and simpler composition. The competing
single-slot map may overconstrain programs if distinct same-head instances
must coexist; the finite-instance row avoids that forced reconciliation but
still needs principality proofs for symbolic inclusion and source-derived
agreement groups. An exact trace set gives a clean reference semantics but is too precise as an inference
requirement when continuation-use tracking would be needed. No alternative is
currently proved sound or principal. The next proof should define the finite
may-effect row denotation and its argument-slot algebra independently, then
derive inclusion, filtering, splitting, residualization, and handler removal
as lemmas; keep exact traces as the soundness reference. Compare the
alternatives on conceptual size, composition, principality relative to the
chosen abstraction, and proof reuse before selecting one.

#### A single abstraction pair for ordinary effect operations (candidate)

The user's preference for a small theory suggests comparing the row-algebra
candidate with an even more semantic presentation. Fix a typed environment,
valuation, semantic environment of closures, activation context `κ`, and a
complete value interface `τ`. Let `Comp_{Γ,ν,κ,τ}` contain the resumable
computation trees of type `τ`
whose closures are compatible with that environment. Concrete computations `c`
are resumable computation trees with their environments and continuation
functions; they are not finite traces. Let `Traces(c)` be the finite request
prefixes generated by executing those computations. Let `α_{Γ,ν,κ,τ}(c)` be
the support of those traces, projected to the chosen typed request domain.
Define
`γ_{Γ,ν,κ,τ}(R) = { c ∈ Comp_{Γ,ν,κ,τ} | α_{Γ,ν,κ,τ}(c) ⊆ R }` over these
resumable computations.
Thus only the abstraction forgets continuation structure; a handler still
receives the actual continuation-bearing computation. The abstract order is
denotational inclusion and its join is union. A function call composes
immediate support with the latent support in the function type. For a fixed
handler transformer `H`, the candidate best sound abstract transfer is

```text
H#_{Γ,ν,κ→κ',τ→τ'}(R) =
  ⋃ { α_{Γ,ν,κ',τ'}(H[c]) | c ∈ γ_{Γ,ν,κ,τ}(R) }
```

`H` is fixed with its source arm clauses and activation context. Its typing
rule must prove that `H` is defined on every member of
`γ_{Γ,ν,κ,τ}(R)`; an
existentially defined subset is not enough for this universal abstraction.
It runs the actual handler/continuation semantics,
including which requests are eligible at each activation, clause effects, and
shallow resume behavior. In the full powerset of the request universe, the
union is the pointwise least transfer; the current finite symbolic-row syntax
may not express it. Any weaker computable row must be proved to over-approximate
this set-valued transfer. By construction,
`α_{Γ,ν,κ,τ}(c) ⊆ R` implies
`α_{Γ,ν,κ',τ'}(H[c]) ⊆ H#_{Γ,ν,κ→κ',τ→τ'}(R)`.

This formulation gives one semantic source for support inclusion and join;
callback contracts compare actual and formal latent effects; subtraction is
not primitive but can remove support only when the handler transformer proves
it absent for every represented computation. Splitting is a set decomposition,
but a handler transformer need not distribute over that split. Generalization,
freshening, and intrusion should preserve the complete relational denotation
under capture-avoiding action. Oracle `Sel_s`, `Demand`, route ledgers, and
type/row/owner maps can then be proof or implementation records for deriving
and transporting that relation. Handler route remains a genuinely distinct
dynamic fact interpreted by concrete `H`, not by separate row selectors.

In the present definition, typed-family formulas and owner incidence are not
inside `α` or `γ`: `α` is only a ground support projection under one valuation.
It would be incorrect to claim that this pair itself preserves the required
symbolic lifecycle. The candidate must be enlarged to one dependent relation
over type valuations, typed row/request views, their source-derived shared-slot
constraints, and the ownership needed to quantify and rename those variables.
`FamAgree` and `Demand` may then be projections/dependency facts of this
relation rather than independent semantic selectors. This is a substantive
enlargement, not a result already proved by the ground abstraction pair.

This economy has a real cost and is not selected. A support row forgets
continuation correlations, so `γ(R)` contains every computation consistent
with the support and may make `H#` substantially more conservative than an
operational example. More critically, request labels need a source-derived
meaning that supports typed-family invariance and operation-signature
coherence. If labels use only family heads, `int` and `bool` requests can be
merged unsafely. If labels carry exact type syntax, subtyping and abstract
denotation must explain how inclusion relates `F<τ>` to `F<υ>` without
introducing an extra per-site rule. The coupled relation must retain symbolic
endpoint and owner incidence through solving, residualization,
generalization, fresh instantiation, and intrusion. A proof that `α` and `γ`
preserve concrete traces does not prove that the resulting constrained scheme
language is principal or effectively solvable.

##### Finite witness for the shallow one-request over-approximation

The support abstraction explains the frozen shallow pair without adding a
one-request source rule. Restrict to one covered operation family `F`, pure
handler arms, and finite resumable trees. The concretization `γ({F})` includes
both the one-request tree `F; return` and the two-request tree `F; F; return`.
For the handler whose arm resumes the raw continuation, transforming the
second tree leaves its second `F` outside the shallow handler. Hence
`F ∈ H#({F})`, even though transforming the one-request tree alone has empty
support. The best sound transfer in this abstraction therefore returns `{F}`.

For a handler whose matching arm ignores the continuation and whose arms are
pure, every tree in `γ({F})` is consumed at its first `F` request and no
continuation suffix is entered. Thus its best sound transfer returns the empty
row. These are direct consequences of one concretization and one relational
handler image. They explain how the abstraction can conservatively reject the
pure annotation for the resuming one-request example while accepting it for
the non-resuming example, without linear or affine usage tracking. They are
only a finite ground witness: typed payload constraints, operation result
types, nested activations, callbacks, symbolic ownership, SCC lifecycle, and
principal finite presentation remain unproved.

Three transfer facts follow once `H#` is defined over this fixed context. It is
monotone because `R ⊆ S` implies
`γ_{Γ,ν,κ,τ}(R) ⊆ γ_{Γ,ν,κ,τ}(S)`. For typed and context-compatible
transformers `H : (κ,τ) → (κ',τ')` then `G : (κ',τ') → (κ'',τ'')`,
`(G ∘ H)#_{Γ,ν,κ→κ'',τ→τ''}(R) ⊆
G#_{Γ,ν,κ'→κ'',τ'→τ''}(H#_{Γ,ν,κ→κ',τ→τ'}(R))`: the two abstract passes are
sound, while re-abstraction between them may add requests. Equality is a
separate completeness property and must not be assumed. The inclusion assumes
that `H` maps every member of its input fiber into the stated output fiber,
and that `G` is defined on every computation admitted by the enlarged
intermediate concretization `γ_{Γ,ν,κ',τ'}(H#_{Γ,ν,κ→κ',τ→τ'}(R))`.
Likewise
`H#(R) ∪ H#(S) ⊆ H#(R ∪ S)` may be strict because `γ(R ∪ S)` contains
computations combining requests from both rows. Thus the handler transformer
need not distribute over row splitting. Repeated pushes with one pop, nested
frames, incomplete handlers, and residual effects are direct tests of that
failure mode.

| Formulation | Conceptual economy | Composition | Principality question | Reusable proof |
| --- | --- | --- | --- | --- |
| Source-indexed `Sel_s` / `RowRel_s` | Highest bookkeeping duplication; mirrors operation sites. | Easy to tune locally, but laws must be re-proved per selector. | Each selector can hide a different non-principal match. | Mostly local. |
| Typed-set algebra (`RowDen`, `RowIncl`, `FamAgree`, `RowRemove`) | One row algebra plus explicit shared-slot agreement and coverage. | Set union/inclusion compose; handler and type relations still meet at explicit proof boundaries. | Constrained denotations may retain inclusion disjunctions; common-witness projection needs proof. | Row and lifecycle lemmas can be reused. |
| Ground abstraction pair (`α`,`γ`) with concrete handler transformer | Smallest ground support core: one order, one concretization, concrete handler semantics. | Every handler instance uses the same transformer; best transfer may be non-effective, too coarse, and need not preserve union. | Pointwise least output says nothing about symbolic matching or scheme projection. | Ground trace soundness and transformer inequalities are reusable. |
| Coupled dependent relational interface | One semantic relation over valuations, typed request rows, shared-slot constraints, and ownership; row/evidence views are projections. | Relational composition is primitive; any abstraction at phase boundaries can still widen. | Must prove least representable residual and fibered-product generalization for independent uses. | One preservation/equivariance theorem may cover solving, handlers, schemes, and intrusion. |

The next useful theorem is to define the coupled dependent relation and prove
that every source computation step and shallow handler step is simulated by
its abstract transfer. Compare its projections with ground typed-set
inclusion; do not assume that the latter carries the symbolic family
constraints. The proof must cover repeated pushes sharing one pop, nested
frames, complete and incomplete handlers, residual effects, and callback
forwarding. Then prove that solving, residualization, generalization, fresh
instantiation, and intrusion preserve the same per-environment solution fiber.
Stop if two source states identified by the proposed relation require different
typed constraints or handler residuals, an escaping request is absent from the
abstract result, or the principal residual cannot be represented. This is a
candidate theorem and does not approve a representation or implementation.

An independent architect delta review (2026-10-01) confirmed that the revised
`γ` must range over resumable computations rather than traces; the handler
input definition above now does so. The review found that the ground
`α`/`γ` transfer remains only a specification: its least output may not be
representable by the finite symbolic row language, composition and union
preservation can be strict, and its support projection loses source-derived
family constraints and owners. The candidate is therefore extended as a
comparison to a coupled dependent relational interface, not accepted as the
successor core. Fixing one valuation also does not prove scheme-level
soundness. Closure of `H` over all computations admitted by `γ`, symbolic
fiber preservation, and principal residual expressibility remain open.

An independent compiler-referee delta review found that support-only
`γ(R)` initially admitted values outside a typed handler's input and did not
state activation-context compatibility. The definition now indexes the
concretization by the well-typed value and activation fiber, requires `H` to
be total on that fiber, and states the corresponding output-fiber premises
for composition. The delta review closed this local domain issue under those
premises. It did not prove source typing establishes those premises for the
proposed coupled relational domain.

#### Coupled interface relation (candidate core)

The common object should be the complete relation of admissible component
interfaces over fixed outer environments, rather than a row plus several
independent selector and demand systems. For a component `C`, let `ρ` assign
its rigid imported identities, `β` its scheme-owned symbolic identities, and
`ν` range over admissible assignments to `β`. Let `I_C` be the complete
observable interface tuple for every SCC root: value types, immediate and
latent typed request rows, and the handler/continuation views whose effects
can escape a root. It must also retain enough occurrence, provenance, and
route coordinates to determine future handler applicability and freshening;
otherwise equal fibers may conceal transport-relevant distinctions. The
candidate denotation is a fiber

```text
Rel_C(ρ) ⊆ { (ν, I_C) }
```

The relation itself contains all correlations among roots, typed requests,
row tails, and effect constraints. The selected source typing rules determine
which pairs belong to it; the type/effect abstract domain determines the
coordinates and their order. A symbolic formula or graph is only a finite
presentation of this relation. Binder scope determines which coordinates are
fixed or quantified, but concrete owner IDs are representation details. A
separate owner ledger is adequate only if a proof connects it to every
owner-sensitive coordinate in the relation.

This gives a common mathematical account of the mechanisms under study:

- `RowIncl` and shared-slot argument invariance restrict which assignments
  and request interfaces belong to `Rel_C`; the latter remains symbolic in
  the relation, including after solving.
- Callback application is a relational composition that joins the callee's
  latent interface with the supplied callback interface under the same typed
  request valuation.
- A handler is a relational image of the shallow handler semantics on the
  continuation-bearing interface. Its residual is assignment-dependent, so
  a coverage fact cannot be frozen before its type fiber is known.
- Row union and splitting are projections/decompositions of interface
  coordinates. They do not license distributing handler transformation over
  a union unless that law follows from the semantics.
- `Sel_s` is a proof witness for a relational premise; `Demand` records a
  dependency used to compute a projection. Neither is a separate source-level
  construct. Route/visibility is a real coordinate of handler applicability
  in the concrete relation, not part of row inclusion.
- Generalization retains the relation over owned binders while fixing `ρ`.
  Fresh instantiation is a capture-avoiding renaming of those coordinates.
  Intrusion acts on the same relation by its parent map and occurrence
  transport. Freshening and injective intrusion are candidates for one
  equivariance theorem. Generalization instead needs exact fixed-`ρ` fiber
  projection and the independent-use product law. Non-injective intrusion
  needs the separate quotient and root-observation theorem.

The natural preservation criterion is equality of each fixed-`ρ` solution
fiber before and after an allowed transformation, with interfaces related by
its induced map. A non-injective parent map needs a quotient theorem proving
that merged fibers preserve every root, callback, request, and handler view.
Independent incoming uses are renamed copies over the same rigid `ρ`; their
joint relation must be the fibered product of the separate copies before
surrounding constraints are applied. This makes typed-family evidence and
handler residuals ordinary parts of one relational denotation instead of
detached records that must be rediscovered after materialization.

This is the most conceptually unified candidate so far, but it is not yet an
inference theory: an unrestricted relation trivially has the needed joins and
projections but may have no finite symbolic representation, terminating
solver, or principal residual in the chosen language. The next theorem must
choose an expressible relation fragment, define declarative source rules for
callback invocation and shallow handlers, prove source-step simulation, and
show that its finite presentations preserve exactly the per-environment
fibers through solve, residualization, generalization, freshening, and
intrusion. If a projection is not finitely representable or loses principality,
the relation needs a principled conservative abstraction, with its acceptance
cost stated. This section does not select the fragment or approve
implementation. The first callback simulation fixture is the frozen accepted
`call(f: () -> [ask] ()) = f()` / `invoke(): [] () = call(\() -> ask::get())`
counterexample recorded later in this note: its abstract relation must retain
`ask` through the call and reject the empty annotation. This pins a concrete
source-to-relation obligation and the allowed final-acceptance difference.

An independent architect review endorsed this as an open consolidation
candidate, with no claim that it defines a solver. The review required the
interface relation to retain the occurrence/provenance/route coordinates
needed by later handler applicability and freshening. It also rejected one
equivariance theorem for every lifecycle step: freshening and injective
intrusion may share equivariance, while generalization needs fiber projection
and the independent-use product law, and non-injective intrusion needs its
quotient/root-observation proof. These distinctions are reflected above;
finite presentation and source-step adequacy remain open.

#### First source-step candidate: callback application

The callback-forwarding Oracle conflict gives a focused test of whether the
relational interface can be generated compositionally. Let `R` range over
typed request bounds with order
`R ⊑ S iff RowDen_A(R) ⊆ RowDen_A(S)` and join `R ⊔ S` given by union. Use a
computation judgment `Γ ⊢ e : T ! R`, where `R` bounds immediate requests
while evaluating `e`. Give function values the latent type `Fun(T, R, U)`:
every invocation of a value at this type has result in `U` and request support
bounded by `R`.

For a first source-step lemma, restrict application to the pure-argument case
`Ea = ∅`. This is enough for the recorded `f ()` callback witness. The rules
below do not define the language's general application semantics:

```text
Γ, x:T ⊢ e : U ! R
────────────────────────────────────── Lambda
Γ ⊢ λx.e : Fun(T, R, U) ! ∅

Γ ⊢ f : Fun(T, Rf, U) ! Ef    Γ ⊢ a : T ! ∅
──────────────────────────────────────────────── App
Γ ⊢ f a : U ! Ef ⊔ Rf

Fun(T, R, U) ≤ Fun(T', R', U')
  when T' ≤ T, R ⊑ R', and U ≤ U'
```

In this pure-argument subcase, call-by-value sequencing contributes no
argument requests. If the source application semantics proves support
composition for the function-evaluation and invocation prefixes, their
support is contained in `Ef ∪ Rf`. This is a conditional upper-bound
calculation; `Ea=∅` alone does not establish the support-composition premise
when continuations can be resumed after state changes. No request-count or
linear-use premise is proposed.
The latent row is looked up from the function value's type, so this same
subcase covers local callbacks, imported callbacks, and generalized functions;
ownership and type substitution act on the complete `Fun` and row coordinates
together. Effect weakening uses `⊑`. The variance condition on latent rows
follows from the meaning of an upper-bound contract: a function with fewer
possible requests may be used where a wider bound is expected. This is a
declarative candidate, not a claim that Yulang source annotations already have
this meaning.

The language's full application rule remains open. Existing runtime
characterization distinguishes pure arguments from computations represented
as deferred thunks, whose effects may occur only if forced. That observation
does not authorize an Oracle-specific mode selector as source semantics. A
successor should derive strict evaluation, delayed computation, and the
activation/handler context in which a deferred effect is observed from one
source-level computation relation. Until that relation is established, this
lemma makes no claim for `Ea ≠ ∅` and does not settle how function argument
effect coordinates interact with latent return effects.

Conditional simulation lemma: assume the function-type interpretation is
sound, a well-typed function value satisfies its latent contract for every
argument in `T` under the call-site type/row instantiation and activation
context, and evaluation composes request traces by concatenation.
Then if `Γ ⊢ f : Fun(T,Rf,U) ! Ef` and `Γ ⊢ a : T ! ∅`, every finite trace
of `f a` has support contained in `Ef ∪ Rf`. Proof: partition the strict
application trace into the finite prefixes from evaluating `f`, evaluating
the pure argument, and the called body's invocation; apply the function and
callback premises and the support-of-concatenation law. Since set union is
the join in the powerset request domain, it is the least upper bound of these
two supplied abstract summaries. It is principal for this *restricted
compositional rule* relative to that domain. It does not prove that all
members of `Rf` are realizable by well-typed functions, or that a finite
symbolic row language has principal solutions for matching and
generalization.

#### Scope correction: pure arguments do not prove support composition

The `Ea=∅` restriction removes requests from evaluating the argument, but it
does not by itself establish the assumed support-of-concatenation law. The
coupled-effect draft gives a stateful multi-shot counterexample to generic
support decomposition: a request continuation can be resumed again after an
appended suffix changes the live store, exposing a request absent from the
independently computed support of the first relation. The same shape can occur
around application if the saved request continuation includes the caller's
post-call context. Thus the bound `Ef ⊔ Rf` is valid only after the source
application relation specifies which continuation suffix belongs to
`Beh(f,x)` and proves that its support is included in those coordinates. A
pure argument is not that proof. The recorded `q`/`g` pattern refutes generic
support decomposition, but it is not yet a typed source program exhibiting an
application-specific failure; this correction withdraws an unconditional
proof premise rather than claiming a new Oracle acceptance counterexample.

For the isolated `ask` forwarding witness, the request is emitted directly by
the callback body before any return into a caller suffix, and there is no
handler between that request and the exported observation. Under that local
source transition premise, ordinary application preserves the observed
`ask`; this suffices to refute the empty row for the witness. Do not extend
that one-request result to arbitrary applications or resumptive handlers.
Those require the complete joint application/continuation relation and a
support projection from that relation, as in the state-threaded bind candidate
in `notes/design/2026-10-01-coupled-effect-interface-core-draft.md`.

On the recorded source witness,
`call(f: () -> [ask] ()) = f()` receives `Rf = {ask}`, so its body bound
contains `ask`. The lambda's latent row therefore contains `ask`, and applying
`call` to `\() -> ask::get()` keeps `ask` in the enclosing result bound. The
explicit `[]` annotation on `invoke` fails. Frozen Oracle `check` accepts this
source but execution reaches an unhandled `ask::get`, so this is a concrete
final-acceptance difference required by the soundness priority. The proof uses
the callback contract semantics and source computation rule; it does not
derive anything from `StackWeight`, `SubtractId`, or the Oracle's route split.

This application lemma establishes neither handler subtraction nor ordinary
effect principality. Proving that a callback's latent contract remains valid
after fresh instantiation and at the receiving activation is still required;
provider visibility and handler eligibility remain separate questions. A
surrounding shallow handler must still transform the continuation-bearing
relational interface, and its output may depend on the type valuation and
activation context. The callback source rule also still needs review against
the language's declarative annotation semantics. Its strong evidence is the
independently witnessed soundness conflict and the standard upper-bound
reading of the callback annotation, not Oracle weight propagation. The next
gate is to establish annotation adequacy, then prove this rule's latent row
constraint remains in the same `Rel_C(ρ)` fiber through generalization, fresh
instantiation, and intrusion.

An independent compiler-referee review found no algebraic error in the
strict sequencing rule under its latent-contract premise: the argument here
is pure, and union is least for the supplied summaries in the powerset row
domain. The review kept the claim conditional on a well-typed callback
satisfying its latent contract after instantiation and in the call-site
activation context. This review does not validate effectful or deferred
arguments. Scheme/route preservation for the pure-argument premise remains
open.

##### Denotational candidates for typed rows

The current `TypedRow` sketch hides the key choice: whether a row has one
payload per family head, or can retain several typed request contracts for
the same runtime operation identity. These are different mathematical
domains, not representation details.

1. **Single-slot family map.** A row maps each family head to one argument
   tuple. Union of two rows that contain the same head must reconcile the two
   tuples. This makes `FamilyCompat` immediate and keeps rows small, but
   `RowUnion` is partial or rejects a program when two compatible execution
   paths use different instances. A join on argument types could fix that only
   if the type domain supplies a sound least join and the effect signature is
   covariant in it; invariant arguments do not supply that rule for free.
   This candidate is compact but has an unproved expressibility/principality
   risk.
2. **Finite set of typed family instances.** A row denotes a finite set of
   symbolic `(FamHead, argument tuple)` instances; request facts carrying
   `OpId`, payload/result signature, latent bounds, and route lineage remain
   attached for handler coverage. `RowUnion` is set union; `RowIncl_A` is
   denotational subset; `FamAgree_A` relates only source-derived shared slots.
   `RowRemove` filters request facts
   only when a complete coverage and route certificate proves removal, then
   projects the survivors back to family instances. Splitting and
   residualization follow from the same set operations. This avoids equating
   requests merely because their family heads match, but symbolic inclusion
   may require disjunctive matching against duplicate target instances.
   Principality therefore depends on whether generalized constraints can
   represent that finite relation or whether a deterministic quotient removes
   the choice without loss.
3. **Support-only solver projection.** A finite support bound (possibly
   `Top`) plus symbolic request/contract records may be a compact solver
   representation of candidate 2. This is bookkeeping, not a distinct
   mathematical core: it is valid only if one denotation-preservation theorem
   proves that the support and symbolic records together retain all family
   instances, typed premises, and route dependencies needed by union,
   inclusion, and removal. Projection to support alone is lossy and cannot
   justify `FamAgree_A` or `Drop`.

The finite set of family instances is the cleanest starting denotation because
union, inclusion, and removal are ordinary set operations; the coarse support
representation is only a solver projection of it. The single-slot map is
smaller only if the source semantics says a family head has one invariant
instantiation per row.
Runtime path matching cannot establish that premise. None is selected: source
operation identity, per-row family uniformity, contract equivalence, the
abstraction function, and least-scheme expressibility are still unproved. The
ground algebra below proves only the basic set laws. The one-arm probe that
follows is a source-level discriminator for whether distinct same-head
instances must be preserved.

The candidates are not yet proven sound, so this comparison describes proof
shape and failure modes rather than selecting a semantics:

| Candidate | Conceptual economy | Composition | Principality risk | Proof reuse |
| --- | --- | --- | --- | --- |
| Single-slot family map | Smallest row domain, but requires a source theorem that each head has one invariant instance per row. | Simple when joins reconcile same-head entries; otherwise union is partial. | A forced reconciliation can reject distinct safe paths; a type join needs independent variance evidence. | Strong reuse if the one-slot invariant is real; otherwise every merge recreates the disputed rule. |
| Finite set of family instances | One support algebra plus one `FamAgree_A` relation over source-derived occurrence groups; handler coverage is a separate semantic fact. | Union and fixed removal compose as set operations; duplicate/open inclusion introduces existential matching. | Eager matching may be non-principal. A relational constrained scheme could retain the whole inclusion formula, if its denotation and generalization are proved. | Row laws and transport can be proved once, then reused by filters, callbacks, and handlers. |
| Support with symbolic contract projection | Compact solver state, but its denotation is candidate 2 plus attached symbolic evidence. | Compositional only if the projection commutes with union, inclusion, removal, and transport. | Same as candidate 2 unless it conservatively forgets distinctions; forgetting needs a least sound abstraction theorem. | Reuses candidate 2's proofs only after representation adequacy is proved. |
| Exact trace sets | Closest to operational meaning and useful as a soundness reference. | Handler sequencing is direct over traces. | Exactness may require continuation usage/linearity and may not have a principal solution in the intended type language. | Good reference for soundness proofs, but weak reuse for an inference solver that intentionally abstracts traces. |

The emerging economy is to keep only two mathematical layers: a chosen
may-effect denotation with `FamAgree_A`, `RowIncl_A`/`RowUnion`, and a handler transformer
whose removal authority is a proof that a request is covered at that activation.
`Sel_s`, `Demand`, solver obligation keys, route lineage, and endpoint/owner
maps then describe how derivations are produced and transported; they are not
independent semantic operators. This remains conditional on showing that the
coverage transformer composes with the chosen abstraction and that its
symbolic constraints have principal least solutions. The family instance
relation and runtime route predicate are different only because the source
semantics asks two different questions (type compatibility versus dispatch
visibility), not because Oracle stores them separately.

If one computation calls the same polymorphic family operation at two
different argument types, a single-slot family row requires the two argument
tuples to satisfy one invariant equation. A contract-set row keeps both
instances and checks a handler parametrically against each request. The
source typing semantics must determine which model applies. If multiple
instances are allowed, candidate 2's inclusion formula needs a principality
analysis; if they are forbidden by the family-indexed row contract, the map
quotient follows from that source invariant. This is a characterization
witness, not a new special-case rule.

There is an existing frozen corpus witness close to this shape:
`tests/yulang/yulang-adversarial-corpus/03_parameterized_effect_capture.yu`
defines one `ask.get` family operation, and `pair()` requests it at `int` and
`str`. Its contract expects the combined, separately specialized handlers to
reject the shared exact operation path at runtime. This is evidence that
multiple typed request occurrences can arise before handler composition, and
that their type arguments do not create different runtime operation
identities. It does not test one handler arm that is itself safe for both
instances, nor does it establish whether a sound successor may reject `pair`
at inference time. Therefore runtime path identity alone does not prove the
single-slot premise; a source typing/acceptance argument for a polymorphic
family row is still required. The frozen fixture is a counterexample search
target, not authority for the successor rule.

##### One-arm discriminator probe

I evaluated a minimal variant with one handler arm whose body ignores both the
payload and continuation:

```yu
pub act ask 'a:
    pub echo: 'a -> 'a

catch (ask::echo 1, ask::echo "s"):
    ask::echo _, k -> (1, "s")
    v -> v
```

Against the frozen binary at `a58eefc31e22141574b6f20c6a5748151c6d79f1`,
`check --no-prelude` exits successfully, while `run --no-prelude --no-cache`
rejects with `conflicting type candidates: int vs std::text::str::str`.
The program's direct shallow trace is `Request(ask.echo, 1, k)`; the handler
returns `(1,"s")` without invoking `k`, so the continuation containing the
second request is never executed. The payload pattern is irrefutable and the
arm result matches the value arm's pair result. Thus the exact shallow
semantics has no type collision on this execution. Oracle accepts its
inference stage but its final specialization rejects it before runtime.

Under the candidate parametric operation-arm rule, the key typing premise is
uniform in the operation parameter `α`:

```text
Γ, payload : α, k : α -> (int * str) ⊢ (1, "s") : int * str
```

The wildcard does not inspect the payload and the body does not use `k`, so
the judgment holds for every `α`. In a shallow handler the operation arm gets
the raw `k`; because the body never invokes it, the suffix is outside the
resulting trace. This proves the local value-transfer case, conditional on the
source rule allowing an operation arm to be checked parametrically at its
declaration binder. It does not establish that rule for other arm bodies.

This is concrete runtime evidence that one operation identity may be reached
with different typed request instances on distinct paths. The `check`/`run`
disagreement is a frozen phase mismatch, not yet a proven source-typing
over-rejection: the candidate's parametric arm premise is still unapproved.
If the source rule is derived and adopted, this becomes a concrete
compatibility expansion (successor acceptance where frozen `run` rejects).
A successor that keeps the family support
projection while retaining typed request contracts separately can check the
single arm against the possible requests without equating unrelated request
occurrences merely because their `FamHead` agrees. The exact trace does not
require a linear continuation type: it only shows this arm does not resume.
The remaining proof is to derive the arm/request compatibility and its
least-solution behavior from source typing, then prove that the coarse
may-request abstraction remains sound when other arms do resume. The proposed
difference is conditional: frozen specialization reconnects the generic
operation effect to one invariant family item, while the candidate checks an
arm uniformly for each request instance. Its source-level validity, including
sharing of captured outer variables, must be proved before treating this
acceptance difference as intentional.

##### Preferred proof candidate: one relation over family instances

The one-arm probe makes candidate 2 the current preferred **proof target**.
The semantic request fact starts from a typed shallow trace: an operation
family head, exact operation identity, family arguments, payload/result types,
and latent effect obligations. A source-origin or occurrence ID is provenance
for transport and route evidence; it is not a new type-semantic distinction
unless handler visibility depends on that lineage. A row value is a finite set
of typed family instances `FamInst = (FamHead, argument tuple)`. Possible
request facts remain attached to this row for handler coverage; they are not
folded into row identity. Thus the two `ask` calls can project to one support
head while retaining distinct `ask<int>` and `ask<str>` instances and their
separate `OpId`/signature evidence.

Use one typed-row denotation for every effect inclusion, with one shared-slot
agreement relation for the type constraints that source rules derive:

```text
FamInst(q) = (family_head(q), q.args)

ArgDen_A(x, ν) = the set of argument tuples admitted by x.args under ν

RowDen_A(R, ν) = ⋃ { {x.head} × ArgDen_A(x, ν) | x ∈ R }

RowIncl_A(R, S, ν) iff
  RowDen_A(R, ν) ⊆ RowDen_A(S, ν)

ArgAgree_A(B, ν) iff
  ⋂ { ArgDen_A(x, ν) | x ∈ B } ≠ ∅

FamAgree_A(B, ν) iff
  all x ∈ B have the same family head and arity
  and ArgAgree_A(B, ν)

FamCompat_A(x, y, ν) = FamAgree_A({x, y}, ν)
```

`B` is a finite indexed family of occurrence views, not a quotient by formula
equality. Equal argument syntax from distinct owners remains distinct in the
transport ledger even though it does not change the mathematical intersection.

`ArgDen_A` is part of the selected abstract type-domain semantics and remains
open for interval and compound arguments. For point-valued arguments it is a
singleton modulo type equivalence, so `FamCompat_A` reduces to mutual subtype
when that relation characterizes the selected equivalence. For interval-valued
arguments it expresses a shared inhabitant, not mutual inclusion of interval
endpoints. Its symbolic formula must encode that denotation; the interval
endpoint and finite-join lemmas later in this note are conditional candidate
implementations. Compound `Con`, tuple, record, and Function arguments need a
structural denotation and adequacy proof before this relation can be solved.
The tuple denotation must preserve dependencies among positions that share
type identities; replacing it with independent per-position sets requires a
separate product proof.

`RowIncl_A` is denotational inclusion of possible typed requests, not pairwise
overlap of row entries. For point-valued finite rows it reduces to ordinary set
inclusion modulo type equivalence. For interval-valued rows it requires every
request admitted by the left row to be admitted by the right; a nonempty
intersection is not enough. The inclusion of `{F<int>}` in
`{F<α>, F<β>}` still denotes a disjunction because the left request must
belong to at least one target denotation.

`FamAgree_A(B,ν)` serves a different, also general purpose: when a source
typing relation requires a finite group `B` of argument occurrences to share
one argument tuple, it says their denotations have a common inhabitant. The
recorded `A/B/C` interval witness has both representative-star pairs
overlapping while all three lack one common inhabitant, so pairwise
compatibility cannot replace a batch relation. The finite-instance row
candidate does not impose a batch merely because family heads agree; source
semantics must establish which occurrences denote one shared family slot.
That grouping feeds the same `FamAgree_A` relation, not a selector per source
site.

The row-match existential is part of the declarative relation, not permission
for the solver to choose one target and discard alternatives. For example,
inclusion of `{F<int>}` in `{F<α>, F<β>}` denotes the disjunction
`FamCompat_A(F<int>,F<α>) ∨ FamCompat_A(F<int>,F<β>)`; for point-valued
arguments this reduces to `(α ≈ int) ∨ (β ≈ int)`. The two branches are
incomparable, so a conjunctive solver cannot choose either one without loss.
This relation alone therefore does not provide a principal *eager* symbolic
solver. A successor can instead keep the whole
`RowIncl_A` formula as one residual relation in its constrained scheme language;
the solver must not select a witness or unify both targets. This is the most
unified current route because it adds no per-site matching construct, but it
shifts the proof obligation: define scheme denotation as all binder
substitutions satisfying the retained relations, then show generalization
projects exactly the environment-independent constraints and yields a
principal denotation. If that language cannot express the relation or its
projection, use a proved principal normalization or an explicitly conservative
abstraction with its acceptance cost recorded.

##### Principality relative to the may-effect abstraction

Let `A` be the selected abstract request domain and `γ_A` its concretization
into finite operation-request prefixes. Soundness is a separate theorem:
every abstract derivation of `Γ ⊢_A e : J` proves
`Traces(e, ω) ⊆ γ_A(effect(J))` for each runtime environment `ω` compatible
with the typing environment and its valuation; inference need not represent
exact continuation-use correlations. Define `Deriv_A(Γ,e)` using only the chosen
declarative source typing rules, including exactly the subsumption, coercion,
and effect weakening rules that source semantics adopts. Oracle behavior does
not add a rule to this set.

A constrained scheme denotes complete interfaces, not just one root type:
all SCC member roots, immediate and latent effect rows, and identities shared
with the environment. `Inst_A(S, ρ)` is the set of those interfaces produced
by one capture-avoiding map for all scheme-owned binders, with the retained
symbolic relations and owned evidence satisfied, while outer identities are
fixed by environment valuation `ρ`. A scheme is valid only when each such
instance yields a derivation in `Deriv_A`. A separate soundness theorem maps
every derivation to its concrete trace bound.

Write `J₀ ≼_A J` when `J` follows from `J₀` using only the declared
subsumption/coercion/effect-weakening rules. Candidate principality requires:

1. every admissible scheme instance is derivable;
2. for every `ρ` and every `J ∈ Deriv_A(Γ_ρ,e)`, there is an
   `J₀ ∈ Inst_A(S,ρ)` with `J₀ ≼_A J`.

If the chosen derivation relation is closed under those rules, this is the
usual most-general scheme property under the preorder `≼_A`. The subtype
equivalence alone is insufficient: strict subtype and row weakening instances
must be covered too. If the source typing relation has no adopted subsumption
rule, the theorem must state that narrower syntax-directed scope rather than
silently closing it under an invented rule.

Keeping `RowIncl_A` as one relation is useful only if its full solution relation
survives every lifecycle phase. For each fixed outer valuation `ρ`, the scheme
must preserve the fiber of local type/row assignments and all dependent views;
projecting constraints cannot choose one existential family match, merge
independent choices, or forget a premise touching a rigid outer anchor.
Solving substitutes symbolic endpoints uniformly and retains any formula
needed by a live view. Residualization preserves the same solution fiber while
moving a relation between live and exported ownership. Generalization keeps
outer identities fixed and quantifies only component-owned binders. Fresh
instantiation renames those binders and their owned relation/evidence
together. Intrusion composes the same capture-avoiding transport through type
parents and separately owned boundary identities, preserving satisfiability
and ownership. Binder quantification alone does not prove this
fiber-preservation condition. These are candidate definitions and laws, not a
proof that the constrained scheme language has principal solutions.

The fiber condition also has a multi-use law. Let `D_ρ = Inst_A(S,ρ)` be the
complete satisfying interfaces for one incoming use. Each use `u` gets its
own injective capture-avoiding binder/evidence map `ιᵤ`; distinct maps have
disjoint local ranges and fix the same rigid outer valuation `ρ`. For a finite
set of incoming uses `U`, the unconstrained joint instances must be the
fibered product `∏ᵤ D_ρ`: each copy preserves the constraints among roots and
evidence inside that use, while no local identity or relation couples two
copies. Constraints from the surrounding program intersect this product only
after instantiation. Internal SCC uses remain attached to one shared live
component and therefore are not factors in this external-use product. The
product law must include dependent row, request, handler, and symbolic
`FamAgree_A` views, not only root types.

A bounded independent architect review found two major gaps in the initial
criterion: equality modulo subtype equivalence omitted strict subsumption and
row weakening, and retaining `RowIncl_A` did not by itself prove exact
generalization across rigid environment anchors. The definition above now uses
the declared judgment preorder and requires per-environment solution-fiber
preservation. Whether source typing adopts those subsumption rules, and
whether the candidate generalization/transport actually preserves each fiber,
remain unproved.

A follow-up compiler-referee review found that a single-use fiber condition
does not imply the independent-use product law. It also required the soundness
statement to quantify compatible runtime environments for open terms. Both
conditions are now explicit above; their proofs remain open.

A separate compiler-referee audit found that literal mutual-subtype `FamCompat`
conflicted with the interval-overlap candidate below, and that independent
pairwise overlaps do not establish an N-way shared argument. The candidate
now separates denotational row inclusion (`RowIncl_A`) from same-slot argument
agreement (`FamAgree_A`), which uses one common witness for a source-derived
batch. Handler removal uses total row inclusion into the arm's accepted typed
domain; a nonempty overlap alone is insufficient. This closes the notation
mismatch only; argument denotations, source batch grouping, total arm coverage,
and their principal symbolic transport remain open.

Oracle compatibility is a separate comparison between final accepted
programs after validation, runtime construction, and specialization. A
constrained scheme can be principal relative to `A` while intentionally
accepting a program the frozen pipeline rejects, or rejecting one it accepts.
Each such difference needs its own concrete witness, the Oracle behavior being
dropped, the successor behavior, and the final-acceptance impact recorded.

`FamAgree_A` is the sole typed-family agreement relation for finite batches;
`FamCompat_A` is its binary instance. The `InvArgs` formulas are symbolic
presentations only where proved equivalent to this denotation. Callback
contracts and concrete filters are instances of `RowIncl_A`; support inclusion
follows from matching equal heads.
`RowUnion` is set union of family instances, so it does not identify two
instances merely because their heads agree. A row split is `RowIncl_A`
evaluated against the union's two parts. Handler removal filters request facts with one
independent coverage predicate, then projects the remaining facts back to
family instances:

```text
Covered_H(q, ν, route) iff
  an exact-operation arm completely covers q
  and RowIncl_A({FamInst(q)}, ArmDomain_H, ν)
  and its payload/resume signature constraints hold
  and q is visible and offered at this handler activation

Q_H = { q ∈ Q | not Covered_H(q, ν, route) }
RowRemove_H(Q, ν, route) = FamInsts(Q_H)
```

For unresolved or interval-valued family arguments, `Covered_H` is a totality
claim over every concrete request represented by `q`, with a valid arm
instantiation for each such request; `ArmDomain_H` is the typed request domain
admitted by the arm's source typing judgment. A nonempty `ArgAgree_A`
intersection is only compatibility; it does not prove complete handler
coverage and cannot justify removal by itself. Until the source arm rule and
this quantification are derived, unresolved request arguments block `Drop`.

Removal is defined on a coupled row/request state, not a possibly partial list
of known requests. Let `E` be the row denotation and `Q` its request evidence.
The required invariant is `E = FamInsts(Q)` for closed rows; open or opaque
sources need an explicit unknown component whose support is `Top` (or another
proved sound upper bound). Coverage may remove only represented facts with
complete certificates; unknown support survives. An empty known `Q` cannot
justify removing a family from a row that may contain an opaque callback
request. The projection and unknown case need one preservation theorem through
solving and transport.

The operation arm is checked parametrically against its operation scheme;
each typed request instance instantiates that scheme under its own capture-
avoiding map. This is the source premise that needs proof. In the probe, the
wildcard payload and unused continuation make the fixed pair arm valid for
both `int` and `str`; the first handled request returns without evaluating
the raw suffix. A row keyed only by `FamHead` instead equates the two argument
vectors before the handler relation runs, producing the conflict under that
candidate source rule. The frozen check/run mismatch is not itself proof that
this rule is the source contract.

This common contract relation removes `Sel_s` from the mathematical core:
operation identity and type arguments come from request elaboration,
`RowIncl_A` supplies effect-bound inclusion, and `Covered_H` supplies the
different runtime/handler fact. A solver may maintain keyed obligations and
`Demand` edges, but they are projections of these relational premises and
their dependent views. Solve substitutions, residuals, generalization,
freshening, and intrusion all transport the same symbolic contracts and
`FamAgree_A` formulas; a family support projection alone never discharges
them.

This is not a selected or approved effect semantics. The remaining principality
gate is symbolic inclusion: for duplicate or open annotation candidates,
`RowIncl_A` contains a finite denotational coverage relation and must either have a principal
residual representation in the scheme language or be conservatively
approximated with its final-acceptance cost recorded. Handler coverage must
also be proved monotone or kept assignment-indexed, and recursive request sets need a finite
least fixed point. The probe establishes a final-stage Oracle behavior
difference for the candidate's minimal closed fragment, conditional on its
source arm rule; it does not prove that rule, the general relation, or the
global compatibility result.

A suitable proof sequence is therefore: derive the per-request arm typing
relation from operation polymorphism and handler application semantics; prove
the finite row-set algebra; lift the relation symbolically and settle the
principality of duplicate/open-row matching; prove the recursive least fixed
point and substitution/binder-transport laws; then connect those laws to the
intrusion parent transport theorem.

##### Ground contract-set algebra (conditional lemma)

Here is a minimal algebraic base for family-instance rows. Fix a finite
universe of canonical family heads and closed, ground argument tuples. Let
`x ≈ y` mean equal family head and mutual subtype of each invariant family
argument. Assume the selected type subtyping is a preorder, so `≈` is an
equivalence relation; quotient family instances by `≈` and write `Q` for the
resulting finite set. Exact operation identity and payload/resume safety are
separate request/handler evidence and are not erased into this row quotient.

Ground rows are finite subsets of `Q`, with:

```text
R ≤ S          iff R ⊆ S
R ⊔ S          = R ∪ S
remove_C(R)    = { q ∈ R | q ∉ C }
```

For fixed `C ⊆ Q` containing only instances whose attached request facts have
already been proved completely covered and route-eligible, `≤` is a partial
order, `⊔` is its least upper bound, and removal is monotone in `R`. Union is
associative, commutative, and idempotent; fixed removal distributes over
union: `remove_C(R ∪ S) = remove_C(R) ∪ remove_C(S)`. A closed filter is
`R ≤ A`. For a split target `A ∪ B`, inclusion is equivalent to
`R = (R ∩ A) ∪ (R ∩ B)` together with both intersections being subsets of
their respective sides. A residual is fixed removal. Thus these operations
need no separate family-pair selector in this ground fragment.

The fixed-`C` premise is essential. In the real typed case,
`C = C_H(ν, route)` depends on a type assignment `ν` and handler evidence.
The denotationally direct residual is therefore assignment-indexed:

```text
Residual_H(R)(ν) = remove_{C_H(ν, route(ν))}(R(ν))
```

A symbolic implementation has to preserve this dependency through solving,
generalization, freshening, and intrusion. Replacing it with the set obtained
under the current solution set can be nonmonotone as type solutions are
refined, as shown by the fixed-evidence monotonicity counterexample below.
The principality question is whether the scheme language can retain this
assignment-indexed relation, or whether a sound coarser row is the least
representable bound. Keeping a detached `FamilyCompat` formula after erasing
the typed request would not preserve the correlation.

This lemma proves only the elementary finite ground algebra, conditional on
the equivalence relation and fixed coverage set. It does not prove source
elaboration, request-to-family projection, handler visibility, symbolic
principal solving, or intrusion transport. It does give a small proof target:
lift the quotient-set operations to symbolic rows by a denotation-preserving
relation, then establish the substitution and binder-renaming laws for that
relation before choosing an implementation representation.

#### Required symbolic typed-family constraint lifecycle

The user has now made an additional mandatory successor invariant explicit:
typed-family argument invariance must remain symbolic throughout solving,
residualization, generalization, fresh instantiation, and intrusion. It must
never be reconstructed only after concrete materialization.

For a source-derived finite batch `B` of same-head family argument
occurrences, the candidate symbolic obligation denotes `FamAgree_A(B,ν)`.
For point-valued argument tuples, the known abbreviation for a binary batch is:

```text
InvArgs(F<τ̄>, F<ῡ>) = ⋀ᵢ (τᵢ <: υᵢ  and  υᵢ <: τᵢ)
```

This `InvArgs` formula is not the general interval or compound formula. The
general symbolic relation must preserve the shared-witness denotation of
`FamAgree_A`, including any cross-position dependence in `B`. The formula
above is valid only where point-valued terms make mutual subtype equivalent to
the selected argument equality. Existing `InvArgs` transport lemmas therefore
cover that point fragment unless their premises are extended to the chosen
`ArgDen_A` semantics.

The chosen typed-row denotation and its `FamAgree_A` relation carry symbolic
argument endpoints and occurrence incidence. Solving substitutes those
endpoints while preserving the
same relational premise; it may discharge that premise only with a recorded
proof (including a symbolic solver proof). It may not drop the relation and
later recreate it by comparing materialized family rows. Row union, inclusion,
removal, and residualization must transport every premise on which their
denotation depends before changing the row representation. The familiar split,
duplicate, filter, callback, and handler cases are candidate derivations from
those relations, not independent semantic triggers. Whether each case follows
from the source rules remains to be proved.

Generalization closes over the symbolic constraint endpoints and maps them
through the same binder ownership as their family arguments. One fresh
instantiation map renames the binders in the row heads and in every
`InvArgs` occurrence consistently. Intrusion applies its type-parent map `P`
to both endpoints and all evidence payloads; hygiene/boundary identities
remain separately transported by `Theta`. Internal SCC uses retain the live
symbolic relation, and independent external uses freshen local binders and
their attached obligations together. This requirement is semantic; the final
constraint representation and proof that each solver/residualization step
preserves it remain open.

The pure type/SCC proof must establish that symbolic family obligations are
part of the transported graph, not auxiliary post-materialization checks. The
effect proof must additionally show that family support projection can erase
argument detail only while this invariant evidence remains coupled to every
request, handler, residual, and scheme view that depends on it. This rules out
the earlier weaker reading in which invariance was generated only when two
already-materialized row heads happened to meet.

#### Review finding: symbolic lifecycle is a requirement, not yet a proof

A focused compiler-referee audit confirms that the phase-transport result
below remains conditional: its premises assume the very generation,
substitution, residual carriage, ownership-aware generalization, and use
freshening rules that a complete proof must establish. The structural
renaming argument does not prove those transitions for an actual machine.
Likewise, retaining formulas in one global `K_sym` set is insufficient if a
generalized root, residual, or use view loses its owner path to the formula.

The delayed open-row case gives a concrete failure mode. Start with
`RowLeq([F<α>], ρ)` and solve `ρ := [F<β>]`. A support-only normalizer that
consumes the relation before recording both `InvArgs(F<α>, F<β>)` and its
dependency on the resulting view admits `α = Int, β = String` under the
candidate typed relation. The formula must be emitted while the symbolic tail
assignment and source occurrence provenance are still available; the
incidence path must then survive generalization and each use. This is stronger
than merely retaining an unowned formula.

The next proof unit is a transition simulation for each actual phase, with
independently source-derived obligation keys and `Demand(view, key)`: show
that every output view still demanded by the source retains a path to
pending/proved symbolic evidence. The open-tail exposure lemma above provides
only the pair-derivation part conditional on occurrence-preserving
substitution; the incidence invariant gives only the target property.
Neither yet proves a concrete solver transition. The compiler-referee audit
also confirmed that mutual subtype is only a shorthand: the common-witness /
cross-bound meaning for interval-valued invariant arguments remains
necessary, so proving transport of the shorthand alone would not close
source semantics. This finding blocks any claim that the typed-family
lifecycle is proved or implementation-ready; it does not weaken the user's
symbolic-retention requirement.

#### Conditional phase-transport lemma and parent-map quotient obligation

For a symbolic obligation `I = InvArgs(F<τ̄>, F<ῡ>)`, type substitution is
homomorphic:

```text
σ(I) = InvArgs(F<σ(τ̄)>, F<σ(ῡ)>)
```

For ordinary structural evaluation of type expressions, this gives the
solution-reindexing identity for any substitution `σ`, including a
non-injective one:
`ν ⊨ σ(K_sym) iff (ν ∘ σ) ⊨ K_sym`. This is a pullback identity; by itself it
does not show that every source assignment or root observation is represented
by the transformed state. Solving may change the endpoints but cannot delete
the relation except with retained proof/equivalence evidence. A
residualization transition is constraint-monotone at this layer:
`K' = K_sym ∪ NewInvArgs`, where `NewInvArgs` is emitted before matched row
heads move or disappear. Generalization binds every local identity occurring
in rows, request facts, and `K_sym` under one ownership map while fixing the
outer environment. Fresh instantiation is one injective capture-avoiding map
on all these occurrences; the existing typed alpha-transport lemma then
preserves and reflects satisfaction. These steps give a conditional
phase-transport result when each phase uses the same symbolic constraint set
and binder ownership.

Intrusion still needs more than this pullback identity. A sufficient simple
case is that the parent map is injective over the symbolic identities in the
jointly observed view, with the outer environment fixed; then it acts as a
renaming and the typed alpha-transport lemma applies. For a non-injective map,
one needs a quotient theorem that states which source assignments and root
observations are intentionally identified and proves the relevant solution
relation both ways. Injectivity is a sufficient condition, not a conclusion
that all parent maps must satisfy.

A simple counterexample rejects unproved collapse of independently owned root
identities. Let two jointly observed roots contain `F<α>` and `F<β>`, with no
source constraint relating `α` and `β`. The source state admits the assignment
`α=int, β=bool`, yielding the distinct root pair
`(F<int>, F<bool>)`. If intrusion maps both identities to one parent `γ` and
exports both roots through that shared parent, its image contains only
`(F<γ>, F<γ>)`; the source assignment and root observation cannot be
represented. This is loss of solution generality/principality for that
interface, not unsound reflection of the substituted `InvArgs` formula.

For `K_sym = {InvArgs(F<α>, F<β>)}`, the pullback equation remains true when
`P(α)=P(β)=γ`; however, whether the resulting quotient preserves the original
source scheme depends on the full root/use observation relation and on whether
the original relation already equates those endpoints for every admissible
assignment. The proof cannot be replaced by comparing concrete family rows
later. The sketch's generic `parent: InnerVar -> BoundaryVar` does not by itself
establish injectivity, a valid quotient, or preservation of symbolic
`InvArgs`. The type/SCC theorem must establish one of these properties for
each jointly observed family constraint and root/use view.

#### Materialization cannot recover a lost symbolic invariant

This gives a direct information-loss witness for the user's requirement.
Assume `ask` is unary and accepts both `Int` and `String`, and that `α` and
`β` are independent well-kinded variables with no other constraints excluding
`α := Int, β := String`. Let `Int` and `String` be incomparable under the
source subtype relation, and consider the same-head comparison

```text
RowLeq([ask<α>], [ask<β>])
```

with support inclusion satisfied. Its typed interpretation requires
`InvArgs(ask<α>, ask<β>)`, so the joint assignment
`α := Int, β := String` is excluded. If an implementation consumes the row
relation while discarding that symbolic obligation, it admits this assignment.
Now consider the later substitution `σ = { α := Int, β := Int }`. Both the
constraint-preserving and constraint-dropping states materialize to the same
closed rows, `[ask<Int>]` and `[ask<Int>]`. A scan of those materialized rows
can only regenerate the reflexive concrete fact for `Int`; it cannot decide
whether the original symbolic state excluded `(Int, String)` assignments.

Formally, materialization at `σ` is not injective over symbolic constraint
states: a state with `InvArgs` and one without it have identical materialized
row observations under `σ`, while their pre-materialization assignment sets
differ. Therefore no reconstruction function of concrete row observations
alone can preserve the original solution relation for both states. The
obligation must be retained symbolically, or be replaced by proof-carrying
evidence whose denotation is equivalent for every assignment before
materialization. This proves necessity of symbolic retention for the selected
typed-row relation; it does not prove that source typing should impose this
relation at every same-head encounter, nor does it define a solver or
residualization algorithm.

The same witness rules out a generic reconstruction interface that receives
only materialized rows while claiming to recover the original symbolic
solution relation. Let `C⁺` be the state retaining `InvArgs` and `C⁻` the state
that discarded it but kept only support inclusion. Under the assumptions
above, `(Int,String) ∉ Sol(C⁺)` and `(Int,String) ∈ Sol(C⁻)`, while
`Mat_σ(C⁺) = Mat_σ(C⁻)` for `σ = {α := Int, β := Int}`. Here `σ` is a lossy
observation probe, not a committed solver refinement; the comparison target is
the pre-`σ` solution sets over `α` and `β`. Any reconstruction function whose
only input is `Mat_σ(C)` must return the same symbolic relation for both
states. That relation cannot equal both original solution sets: admitting the
distinguishing assignment is wrong for `C⁺`, while rejecting it is too strong
for `C⁻`.

Consequently, a phase that discards the original obligation before committing
any substitution and then relies only on concrete row observations to recover
the original generalized relation cannot preserve that relation. It must
transport the symbolic obligation or equivalent proof/evidence. This does not
apply to an ordinary solver rewrite after a committed substitution when
equivalence is required only over remaining assignments under that
substitution; such a rewrite needs its own solution-preservation proof.

#### Conditional `InvArgs` transport theorem for an injective parent map

This gives a sufficient proof route for the user's symbolic-lifecycle
requirement. Let the complete typed view be
`S = (Roots, Rows, Q, H, G, C, K_sym, Γ)`, where `H` contains handler facts,
`G` grant/annotation facts, and `C` the remaining typed constraints and
evidence. Define `Ids(S)` as every type identity occurring in these fields,
including proof/equivalence evidence payloads and `FV(Γ)`, partitioned by
ownership into locally generalizable identities, retained internal/live
identities, fixed outer anchors, and selected boundary identities. These
classes are disjoint for a given transition; a boundary identity is mapped to
a parent only in the intrusion transition that selects it. Each phase states
its bind/freshen/fix sets explicitly: an external use freshens
component-owned binders, an internal SCC use keeps retained live identities,
and outer anchors stay fixed.
`Tr_P` is the homomorphic action of a typed identity renaming on all
type-bearing fields and evidence; it leaves family heads, `OpId`s, and
source/evidence labels fixed. For intrusion, the map is identity on retained
internal identities and outer anchors, and maps only selected boundary
identities to fresh parent identities. Generalizable identities not selected
for that boundary follow their owning binder map. The map over the complete
view must be injective, with parent destinations disjoint from retained
identities and anchors.

Assume (i) type-expression evaluation and subtype satisfaction commute with
this capture-avoiding renaming; (ii) each same-head row interaction emits its
symbolic `InvArgs` obligation before splitting, subtracting, moving, or
residualizing a head; (iii) solving applies its substitution uniformly to
all type-bearing fields and `K_sym`, retaining proof evidence for any
discharged constraint; (iv) residualization carries forward all of `K_sym`
and adds newly emitted obligations from interactions represented in `H`,
`G`, `C`, or `Rows`; and (v) generalization binds only locally generalizable
identities in `K_sym`, retaining mixed constraints with outer anchors fixed.
Each independent use has an injective freshening map; their local ranges are
pairwise disjoint and avoid all fixed anchors.

Then:

1. **Solve transport:** for any solver substitution `σ` and assignment `ν`,
   `ν ⊨ σ(K_sym)` iff `(ν ∘ σ) ⊨ K_sym`. This is the structural substitution
   identity; it does not claim that a non-injective `σ` is a bijection on
   source assignments.
2. **Residual transport:** every pre-existing symbolic obligation remains in
   the residual evidence (or as proof-carrying solved evidence), and every
   constraint created by a matched family interaction in the represented
   typed view is present before its row heads disappear. Thus residualization
   cannot lose `InvArgs` by losing the only visible copy of a family head.
3. **Generalization/use transport:** the generalized component closes over
   component-owned identities in `K_sym` together with root/row identities;
   retained internal/live endpoints stay shared on internal SCC uses, while
   outer endpoints remain fixed anchors. An external-use map freshens its
   component-owned binders across rows and constraints together, giving the
   alpha-equivalent constraint view. Independent external-use maps have
   pairwise disjoint local ranges and preserve shared outer anchors.
4. **Intrusion transport:** injectivity and freshness make `P` a
   capture-avoiding renaming on the complete typed view. In particular,
   `Tr_P(InvArgs(F<τ̄>,F<ῡ>)) =
   InvArgs(F<P(τ̄)>,F<P(ῡ)>)`, so typed alpha-transport preserves and reflects
   its solutions and the symbolic relation remains available after the parent
   graph is formed.

The proof is structural: substitution evaluation commutes by induction on
type expressions; residualization preserves the constraint ledger by its
explicit union rule; binder and parent maps are injective renamings fixing the
outer environment; and `InvArgs` is built only from those type expressions.
Composition gives the stated phase-by-phase transport for this complete typed
view, conditional on every phase actually maintaining the listed fields and
ownership partition. This does not prove Oracle view completeness, that the
proposed intrusion allocator actually chooses an injective map over the
complete typed view, callback/handler visibility, row/effect principality, or
final acceptance. Those premises and the non-injective quotient alternative
remain open.

#### Symbolic family-constraint incidence invariant (candidate)

The phase theorem above treats `K_sym` as a set of formulas. To make its
required coupling to the typed effect view explicit, model it as an abstract
incidence ledger rather than as a constraint set recovered from current row
heads:

```text
κ = (formula, endpoints, source_origins, use_occurrences, state)
formula = InvArgs(F<τ̄>, F<ῡ>)
state   = Pending | Proved(proof)
```

`source_origins` are immutable source provenance labels; `use_occurrences`
are fresh elaboration/view identities for this occurrence in a particular
component or instantiated use. Independent uses preserve the provenance label
but get disjoint use-occurrence IDs and cloned ledger records/owner edges.
These are abstract source/evidence identities, not concrete materialized
family rows. A formula may be `Proved` only with evidence that remains
transportable with its symbolic endpoints. It may not transition to an
unlinked `Discharged` state.

Define an obligation key `o` independently from the ledger record. Candidate
identity fields are `(source_site, relation_kind, family_head,
argument_position, source_pair_or_batch_id, view_occurrence_id)`; symbolic
endpoint terms are formula payload, not key identity. A type substitution
changes those endpoints without minting a new obligation or breaking its
incidence. Fresh instantiation maps `view_occurrence_id` with the
occurrence-owner map, while intrusion transports it with graph map `M`; source
provenance and relation kind remain fixed. This stable-identity choice is a
candidate bookkeeping invariant, not a selected representation.
Each source rule that relates same-head family instances derives this key
before row movement. Define `Demand(v, o)` independently from the ledger: it
holds when the source typing derivation for live view `v` uses that
family-argument equality to type, match, resume, export, or constrain the
view. For each transition, derive the output `Demand` relation and
transported obligation keys from source-rule premises and transition
correspondence, not from ledger owner edges. The owner relation is directed
`κ -> v`; its transitive closure allows a component/root view to retain the
obligation through intermediate residual, handler, or continuation views.
The invariant is: for every live `v` and independently derived key `o` with
`Demand(v, o)`, there is a `Pending`/`Proved` ledger record `κ` representing
the transported `o` and a path from `κ` to `v`, with endpoints equal after the
phase's uniform substitution or alpha map. If a transition removes an input
view, each output view that still satisfies `Demand` for the transported key
must retain a path to its record. Erasing both the dependence and owner edge
cannot establish preservation; the dependence relation and key come from the
source derivation independently.

Row splitting, handler matching, subtraction, and residualization create a
record before removing/moving a family head and transfer edges to every
resulting dependent view. Solving substitutes formula endpoints and proof
payload uniformly. Generalization closes over locally owned endpoint IDs and
transports owner edges. Fresh instantiation renames endpoints and use
occurrences together, preserves source provenance, and clones the relevant
record/owner subgraph for each use. For open rows, solving also includes tail
assignment, unification, and normalization: before any such step consumes or
replaces a symbolic `RowLeq`, it must inspect the relation's retained
occurrence provenance and derive every same-head `InvArgs` key and `Demand`
edge implied by the newly exposed symbolic pair. Record the key and incidence
before replacing the relation; they cannot be recovered later from a
materialized closed row. If derivation is not yet available, retain the
original `RowLeq` or a two-way solution-equivalent residual that preserves its
provenance and dependent typed views. Intrusion needs a graph map `M` over all
live view and evidence vertices, in addition to type map `P` and hygiene map
`Theta`. `M` must preserve and reflect typed dependency incidence (or satisfy
a separately proved quotient condition); `P` maps formula endpoints, and
`Theta` maps only the relevant handler/hygiene identities. Support projection
may discard family arguments from `E`, but it cannot delete ledger records or
owner paths from `Q`, `H`, `C`, residual constraints, or the component graph
while `Demand` remains true.

This incidence invariant strengthens the earlier set-level transport
condition: `K_sym' = K_sym ∪ NewInvArgs` alone is insufficient if the newly
added formula is detached from the result view that relies on it. The
invariant can be proved phase by phase by checking (a) source derivation of
`Demand` and obligation keys, (b) same-head constraint generation including
delayed pairs exposed by symbolic open-tail normalization, (c) substitution
of formula and proof evidence, (d) preservation of dependency incidence
during residualization, (e) source-label preservation plus per-use record
cloning and key transport, and (f) incidence-preserving graph
transport during intrusion. The intrusion graph map `M` preserves and
reflects incidence relative to independently derived `Demand` and commutes
with `P` on typed endpoints and `Theta` on hygiene identities. Until these
transition rules and their source ownership are proved, this remains an
abstract proof obligation, not a selected storage representation or
implementation contract.

#### Conditional incidence preservation for a fresh use copy

One phase can be isolated as a graph-copy lemma. Let `G` be the incidence
subgraph for one generalized root and its live dependent typed views. For
every independently source-derived `Demand(v,o)` in that set, `G` contains a
record representing `o` and the complete owner path from that record to `v`;
thus closure traverses incoming `κ -> v` edges to include their obligation
records, as well as all dependent views in the component. Let external-use
instantiation copy exactly the ledger/view vertices and owner edges of `G`
using an incidence-graph isomorphism `j` on ledger-record, use-view, and
obligation-occurrence identities, and an injective map `ι` on component-owned
type identities. The image of local type identities
under `ι` is disjoint from fixed outer anchors; `ι` fixes those anchors. The
isomorphism `j` preserves source-origin labels and gives this use a range
disjoint from every other external use. Assume the independent source-derived
`Demand` relation commutes with the copy: an output view demands key `j(o)`
exactly when its preimage demands `o`, where key transport `j(o)` means the
use-occurrence identity is mapped by `j`, symbolic type endpoints by `ι`, and
source-origin labels remain fixed.

Then the copy preserves the incidence invariant in both directions. Each
owner path `κ ->* v` maps edge-by-edge to `j(κ) ->* j(v)`, and every path
inside the copied incidence graph has a preimage because the copy is an
isomorphism. Formula endpoints are transformed by `ι`, so an
`InvArgs` record remains the same symbolic relation up to the injective type
renaming; pending/proved state and transportable proof evidence are copied
with it. Disjoint ranges prevent obligations from separate instantiations
from being accidentally merged, while fixed anchors remain shared. The proof
is induction on path length plus the assumed commutation of `Demand` and the
homomorphic formula action.

This establishes the graph-theoretic obligation for a use-copy transition
that satisfies these premises. It does not prove the premises for a proposed
instantiator, choose the ledger representation, or establish that the
candidate interval-valued invariant relation is transported by the selected
type renaming. It also says nothing about internal SCC uses, which retain live
component identities rather than copying this subgraph.

#### Delayed open-row family obligations (conditional solver rule)

An open relation can constrain family arguments before the compared heads
exist syntactically in the same row expression. For example,
`RowLeq([F<α>], ρ)` followed by a symbolic tail solution
`ρ := [F<β>]` exposes a same-head pair. The solver must not consume the
`RowLeq` merely because its current support projection is satisfiable. Before
replacing or discharging it, normalization derives
`InvArgs(F<α>, F<β>)` and the corresponding `Demand`/owner incidence from the
original relation and its occurrence provenance, then transports both through
the same substitution. The derivation uses the original relation together
with the symbolic tail assignment and both sides' occurrence provenance. If
the relation does not carry enough provenance to
derive that obligation while still symbolic, it remains as a residual
relation; concrete row materialization is not a fallback obligation
generator. This rule is conditional on the open-row denotation's occurrence
provenance being sufficient to identify both endpoints and dependent views.
It does not yet prove that a proposed solver can discover all such pairs,
terminate, or preserve the complete joint solution set.

#### Relation-driven obligation exposure (unified direction)

The earlier `Sel_s` notation over-factored the semantics. Following the user's
conceptual-economy requirement, it is not a proposed semantic selector or a
new construct per source site. The preferred direction is one denotational
typed-row relation/algebra; family-argument formulas arise from evaluating
that relation and its row operations. A source typing rule may invoke a
general relation on particular operands, but it does not define a private
same-head matching algorithm. `Sel_s` may be used temporarily in proofs to
name the occurrence pairs exposed by an evaluation; `Demand` names the
proof/implementation dependency of observed views on a relational premise.
Neither belongs to the mathematical core if the common relation can derive
them.

The all-pairs `Pairs_F` relation below is retained only as a maximal stress
case for whether the incidence bookkeeping can preserve duplicate and
cross-row obligations. It does not assert that every same-head encounter
requires invariance. The relation denotation must decide which obligations
exist uniformly; transport then maps that relation and its complete evidence
graph. The exposure proof below establishes a property only for the all-pairs
stress instance, not the unified relation itself or any source rule.

#### Open-tail obligation exposure lemma (conditional)

This makes the delayed rule's preservation claim explicit. Let `R₁,R₂` be
open row expressions with occurrence-bearing tails, and let `μ` assign each
tail a closed occurrence collection. Define `Occ(R,μ)` by concatenating the
explicit occurrences with the assigned tail occurrences while preserving
duplicates and owner identities. For family `F`, define
`Pairs_F(R₁,R₂,μ)` as a tagged union of (i) every distinct same-head pair
within `Occ(R₁,μ)`, (ii) every distinct same-head pair within `Occ(R₂,μ)`,
and (iii) every same-head cross-row pair in
`Occ(R₁,μ) × Occ(R₂,μ)`. Each pair retains its category, both endpoint
owners, and the originating `RowLeq` relation identity; it contributes its
`InvArgs` formula and corresponding `Demand` incidence.

If a symbolic tail substitution `σ` replaces a tail with an occurrence-bearing
row term and `μ'` assigns any remaining tails in the substituted expressions,
with `μ` and `μ'` related so the evaluated closed rows agree up to the
substitution's occurrence transport, and that transport induces a bijection
`T` on the occurrence identities of each evaluated row, then
`T(Pairs_F(R₁,R₂,μ)) = Pairs_F(σ(R₁),σ(R₂),μ')`. In particular, a pair
introduced by expanding a tail is derivable from the still-symbolic relation
and the symbolic tail assignment before the relation is consumed. No pair
needs to be inferred by scanning a separately materialized final row. This
follows by induction on row concatenation: explicit occurrences are preserved,
each assigned-tail occurrence is inserted once with its owner, and the
within-row pair, cross-row pair, and family-head filters commute with that
insertion. The bijection `T` therefore preserves pair tags, endpoint owners,
and duplicate occurrences throughout.

The lemma depends on occurrence-preserving substitution and on the related
assignment premise; it does not establish either for a concrete solver. It
also does not show that every source typing rule should create each of these
pair obligations, only that the declared typed `RowLeq` denotation exposes
the full within-row and cross-row pair set.
The source judgment must establish that this is the right comparison
relation. Until then the result is a conditional bridge from symbolic tail
expansion to the delayed obligation rule, not a solver correctness theorem.

#### Entailed known-pair obligations while tails remain open (conditional lemma)

There is a safe partial-solving step before tails are committed. Write each
open row as its explicit occurrence list concatenated with its unknown tails.
Let `O_known(R₁,R₂)` contain the keyed same-head pairs that can be formed
using only explicit occurrences: within each explicit side and across the
two explicit sides. Each key retains the originating `RowLeq`, pair category,
and both occurrence owners. Let `C` be the other current constraints. Derive
`Demand(v,o)` independently from source typing for each output view `v` and
key `o`; do not infer it from the ledger edges being constructed.

For every occurrence-preserving assignment `μ` to the unknown tails, the
explicit occurrence lists embed into `Occ(R₁,μ)` and `Occ(R₂,μ)`. Therefore
every key in `O_known` is also a key in `O_open(R₁,R₂,μ)`. Under the candidate
assignment-wise `TypedRowLeq` denotation, satisfying `r` entails every
formula in the projection of `O_known`, for every remaining type assignment
`ν`. So this transition is solution-preserving:

```text
C ∧ r  ==>  C ∧ r ∧ formulas(O_known)
```

The reverse implication follows because `r` remains in the output. Keep the
full keyed `O_known` ledger records even when formula text duplicates another
record, and add an owner path to each view `v` for which `Demand(v,o)` holds.
Apply subsequent type and tail substitutions uniformly to `r`,
these formulas, their occurrence owners, and the incidence edges. When later
tail assignments expose additional pairs, derive the full `O_open` from the
still-live symbolic relation and add newly exposed keyed records before any
equivalent closed-tail extraction. Reuse matching transported keys and their
existing evidence/owner edges; do not duplicate or silently replace them. Do
not remove `r` while tails remain unresolved unless a residual has separately
been proved equivalent for all remaining assignments.

This proves a narrow open-tail constraint-generation rule: known symbolic
family obligations may be emitted early because they are entailed by every
satisfying assignment of the retained relation, while unknown-tail obligations
remain pending in `r`. It does not prove that arbitrary source constructs use
this candidate typed-row denotation, nor that a concrete solver maintains the
occurrence injection, independently derived `Demand`, or uniform substitutions.
Interval-valued invariant arguments still require the separately selected
common-witness relation, and the proof must then use that relation's formula
projection in place of the current `InvArgs` shorthand.

For a uniform type substitution `σ` and row substitution `τ`, require an
injective occurrence embedding `T` for all old explicit occurrence IDs. `T`
preserves each occurrence's left/right side and originating relation, and
every old explicit occurrence remains explicit in the substituted syntax.
Map each existing key
`(r, category, o₁, o₂)` to `(r, category, T(o₁), T(o₂))`, applying `σ` to its
symbolic type endpoints. Existing keys are preserved in the new collection:

```text
Tr_(σ,τ)(O_known(R₁,R₂)) ⊆ O_known(σ(τ(R₁)), σ(τ(R₂)))
```

The inclusion follows because every old explicit occurrence remains in the
substituted row with its transported owner, while a tail substitution may
expose additional pairs. Those new keys are generated before the relation is
consumed, as in the closed-tail extraction rule, and are entailed by `RowLeq`
for the committed tail assignment. For every type assignment `ν`, formula
satisfaction on the transported old-key collection is equivalent to
satisfaction on the source collection under the pullback `ν ∘ σ`.
The identity map on old keys remains one-to-one even when `σ` is
non-injective: different occurrence pairs may now carry identical formula
text, but their keyed records and `Demand` edges are not coalesced. This is a
pullback preservation statement, not a surjectivity claim about the solver's
solution space. It gives a local solve-transport law for early obligations;
concrete substitution generation and independent `Demand` commutation remain
premises.

#### Assignment-wise open typed-row characterization (conditional lemma)

For a fixed joint assignment `(ν,μ)` to type variables and row tails, write
`r₁ = Occ(R₁,μ)` and `r₂ = Occ(R₂,μ)`. Define
`O_open(R₁,R₂,μ)` as the keyed collection of `(pair, InvArgs(...))` for each
tagged within-left, within-right, and cross-row pair in `Pairs_F`, over every
family head `F`. This collection keeps duplicate pair keys and owner incidence.
Let `K_open` be its formula projection, which may collapse equal formulas.
Define assignment-wise typed coverage by the chosen open-row relation:

```text
TypedRowLeq_ν,μ(R₁,R₂) iff
  support(r₁) ⊆ support(r₂)
  and ν satisfies K_open(R₁,R₂,μ)
```

Then the formula projection of the pair-obligation generator is exact for
this relation at each fixed assignment: its structural support check and
emitted `K_open` hold exactly when `TypedRowLeq_ν,μ` holds. The keyed
collection `O_open`, rather than its formula projection, is the object that
must be transported to preserve duplicate owner incidence. Consequently, the
set of satisfying joint assignments is exactly the denotation of the retained
symbolic `RowLeq` when the latter is interpreted by this assignment-wise
relation. Tail expansion
does not add a heuristic constraint: the exposure lemma gives a bijective
correspondence between the obligations before and after occurrence-preserving
substitution, including duplicates and owners. When support inclusion passes,
no additional same-head argument atom is needed for this selected relation,
and deleting a non-entailed emitted formula would admit an assignment outside
it. This is pointwise exactness, not a normalization algorithm; it does not
permit deleting duplicate keyed obligations or their incidence merely because
their formulas are equal.

The conclusion is conditional on choosing this typed relation as the source
meaning of `RowLeq`. It does not prove that callback compatibility, handler
matching, or any source construct should be governed by this relation; it
does not establish termination, principal solving over unknown tails, or
global effect principality. Those need independent source and solver proofs.

#### Exact obligation extraction at a committed closed-tail solve (conditional lemma)

This isolates a sound symbolic replacement step once a solver has committed
row-tail assignments that close both sides. Let a live constraint record
`r = RowLeq(R₁,R₂)` carry the occurrence provenance and dependent typed-view
identities required by the preceding incidence invariant. Let `μ` be the
committed, occurrence-preserving tail substitution such that both
`Occ(R₁,μ)` and `Occ(R₂,μ)` are closed finite occurrence collections. The
substitution is applied uniformly to the complete live typed view, all
existing symbolic obligations, and their owner edges. The transition then
evaluates the support inclusion and reconciles the full keyed collection
`O_open(R₁,R₂,μ)` with existing records for `r`:

```text
if support(r₁) ⊄ support(r₂): retain a failing support certificate for r
otherwise: replace r by the reconciled O_open ledger and its support certificate
```

The replacement is symbolic: each record in `O_open` contains the original
family head, symbolic argument endpoints after `μ`, source origins, pair
category, endpoint occurrence owners, and the original relation identity.
Reuse each existing record whose transported key occurs in `O_open`,
preserving its pending/proved state, proof evidence, and owner edges. Add only
absent keys; if distinct keys share formula text, retain both records.
Transfer the `r` owner paths to every output view that remains independently
`Demand`-dependent on these facts; do not replace the keyed collection with
its deduplicated formula projection. If the row-tail assignment is not
committed and closed, this step is unavailable: keep `RowLeq` symbolic (or a
two-way solution-equivalent residual), since the unknown tail may expose new
heads and pairs.

For any fixed remaining type assignment `ν`, the input constraint holds
exactly when support inclusion passes and `ν` satisfies the formula
projection of `O_open`, by the assignment-wise characterization above. Thus
the replacement preserves and reflects the solution set over remaining type
assignments. Each output formula remains symbolic in its endpoints; no later
comparison of concrete materialized family rows participates. The keyed
collection plus transferred owner paths also preserves the declared
incidence invariant for every dependent output view. If support inclusion
fails, the retained failure certificate denotes the empty solution set for
that committed tail assignment, inherits `r`'s dependent-view owner links,
and prevents publication of a successful dependent output view before the
rejection. Preserve any existing keyed records and their proof/owner state
alongside that certificate until rejection is published.

This is a local solution-preserving transition under the candidate
assignment-wise `TypedRowLeq` and its `InvArgs` formula semantics. It does not
prove that a real solver commits tails with this occurrence transport, that
source typing selects this open relation, or that mutual subtype is the
correct invariant relation for interval-valued arguments. It also does not
solve principality while tails remain open. Those remain separate obligations;
the specific transition here proves how to consume a `RowLeq` without losing
symbolic argument invariance after its tails have been committed.

#### Source-rule derivation of family obligation keys (candidate)

The source-rule audit gives a concrete candidate derivation point for the
independent obligation keys above. The frozen effect-subtraction spec says
same-path family arguments meeting in listed row set operations are
constrained invariantly. The principal-monomorphization spec reconnects a
generic operation's return effect to the corresponding typed family item in a
handler's scrutinee row. The runtime spec matches requests by exact operation
path. These are characterization evidence: they do not define successor
source typing, callback argument comparison, or handler eligibility, and
they do not authorize Oracle weight routing.

The source audit supports the following narrow applicability map:

| Relation site | Frozen source evidence | Successor status |
| --- | --- | --- |
| Row split at the common weighted heads | The effect-subtraction spec names `K ∩ Common(L)` and requires invariant argument constraints when the same-path items meet there. | Characterization target; derive a keyed obligation before splitting. |
| Residual subtraction | The spec names `L - J` and same-path family argument constraints at residual subtraction. | Characterization target; move or retain the same obligation and owner evidence with the residual. |
| Duplicate row-head collection | The spec requires same-path family arguments to constrain invariantly when duplicate heads are collected. | Characterization target; equal formula text does not erase occurrence ownership. |
| Concrete filter check | The spec checks same-path typed family items against the annotation and requires invariant arguments; checked filter metadata is then removed from replay. | Characterization target; retain proof evidence if any later view still depends on the check. |
| `Neg::Stack` common-stack check | The spec explicitly includes common-stack matching among invariant sites. | Characterization target; keep the relation attached to the stack-derived view. |
| Generic callback/Function row comparison | Principal monomorphization matches effect-row items by family and emits subtype constraints in its specialization graph, but this is not a source typing rule requiring invariant comparison for every actual/formal same-head pair. | Candidate successor rule only; prove it from callback typing and the selected effect abstraction. |
| Arbitrary open `RowLeq` and all same-head occurrence pairs | The frozen list does not define this general relation. | Candidate denotation only; prove source adequacy and solver principality before selecting it. |

#### Closed point-row filter as a `RowIncl_A` instance (conditional lemma)

This is a check of whether the unified row relation can derive a frozen,
closed filter case; it adds no filter-specific family semantics. Assume
`RowIncl_A(E,A,ν)` denotes typed request inclusion, closed actual and annotation
rows contain at most one typed occurrence per family head, their argument
terms denote point values, and `≈` is the source type equivalence used for
invariant family arguments. Write the filter's acceptance condition as the
following derived abbreviation:

```text
FilterOK(E,A) iff
  support(E) ⊆ support(A)
  and for each F<τ̄> in E, the unique F<ῡ> in A satisfies τ̄ ≈ ῡ
```

The generic row relation compares the unique same-head occurrences for each
`F` in `support(E)`. For each argument position `i`, its symbolic formula
encodes `τᵢ ≈ υᵢ`, keyed by the relation identity, both occurrence owners,
`F`, `i`, and the checked-view occurrence. `FilterOK` then holds under
assignment `ν` exactly when support inclusion passes and `ν` satisfies the
row relation's formulas. If a family is absent from `A`, the support check
fails; there is no same-head formula to reconstruct later.

For this fragment, the lifecycle action is direct: solving substitutes each
formula endpoint while retaining its stable key and owner incidence; a proof
may discharge it only while preserving proof evidence for every still-
demanding checked view. Residualization transfers the record to each output
whose derivation used the check. Generalization maps local endpoint binders
and their row owners together while fixing outer anchors. Fresh instantiation
clones the demanded incidence subgraph and applies one capture-avoiding map to
both endpoints and occurrence owners. Injective intrusion transport applies
the type-parent map to endpoints and the graph map to keys/owner edges; a
non-injective map still needs its separate quotient proof. These are the
conditional transport lemmas already stated above instantiated at a
deterministic source selector, not proof that an actual successor machine
implements the transitions.

The premises matter. Duplicate family heads make annotation matching
non-unique and may require one batch common-witness formula; open rows require
the source selector to operate on symbolic occurrences and preserve delayed
matches; interval-valued arguments need the common-witness relation, not
point equivalence. This lemma therefore settles only a closed point-row
filter subcase. It neither derives handler visibility nor validates any
Oracle weight route.

#### Interval-valued family agreement (conditional lemma)

For one argument position `i`, assume the selected type-domain semantics
soundly decomposes two symbolic argument descriptions into finite endpoint
sets `[L_x,U_x]` and `[L_y,U_y]`. If the general `FamAgree_A` relation means
that these descriptions have one shared witness, the candidate proof formula
is:

```text
MeetKey(relation, x_owner, y_owner, F, i, dependent_view)
MeetFormula(i) = { l <: u | l ∈ L_x ∪ L_y, u ∈ U_x ∪ U_y }
```

Assuming both input intervals are feasible and the selected carrier has the
finite interval-realization property, `MeetFormula(i)` is satisfiable exactly
when the two descriptions have a common argument witness. This is the
two-occurrence instance of the N-way endpoint lemma below. It is a possible
symbolic characterization of binary `FamAgree_A`, not a filter-specific semantic
construct. Whether source-level shared-slot agreement should mean common witness
or another relation is still open.

Keep the proof key and symbolic endpoints through solving, residualization,
generalization, fresh instantiation, and intrusion. The previously stated
substitution and alpha-transport laws apply to the formulas and owner graph;
if normalization derives the cross-bound inequalities, it must retain the
batch record/proof and every dependent-view path. It may not replace the
symbolic obligation with a materialized join witness. This lemma applies only
under a carrier premise. Accurate decomposition of compound argument types,
the actual successor carrier, and the source proof that this is the right
`FamAgree_A` relation remain open, so this is not an implementation rule.

The table below is a frozen-Oracle characterization crosswalk, not a set of
successor rules or implementation tasks. It records which operands its
current implementation relates so a separately defined declarative row
algebra can be tested against them. For the successor, obligation keys belong
to relational premises and identify the relation, endpoint owners, family,
and argument position; source sites do not get private selectors by default.

| Site | Candidate endpoint group to inspect before mutation | Views whose `Demand` must be derived from the source rule |
| --- | --- | --- |
| Row split `K ∩ Common(L)` | A row occurrence in `K` and the stack occurrences that make the same family available in the common set. | The source row and the split head/residual constraints that carry the selected family. |
| Residual subtraction `L - J` | A removed family occurrence in `J` and each pushed-family occurrence whose payload is restricted by that removal. | The transformed residual weight and every row/tail constraint that consumes it. |
| Duplicate collection | The occurrences in one source-defined collection that are coalesced to one family entry. The invariant formula may be a batch common-witness obligation, not an arbitrary star of pairwise formulas. | The collected output entry and any constraints whose payload used the removed duplicates. |
| Concrete filter check | An incoming typed family occurrence and each same-head annotation occurrence that the check actually compares. | The checked source bound/result; retain proof evidence if a later view relies on the check. |
| Common-stack check | Stack occurrences used by the source's common-frame operation, plus a typed row occurrence only when that rule compares it to the resulting common set. | The stack-derived row/inner view and any residual view that uses the match. |
| Callback actual/formal comparison | Only the pairs selected by a separately approved callback typing rule; the actual/formal cross-pair is currently a conjecture. | The application result and callback contract views only if that rule makes them depend on the comparison. |

This is a source-site checklist, not a selected pairing function. In
particular, the first/representative item chosen by frozen
`collect_neg_effect_items` is not a principled source identity, and the
Oracle's weighted stack route does not decide the successor `Demand` edges.
For each site, source semantics must establish the group, argument relation,
and every dependent output independently; then the solver can attach the
symbolic record before the row or frame mutation. The current evidence does
not yet supply those derivations.

The frozen implementation provides a source-code crosswalk for these named
characterization sites. At revision `a58eefc31e22141574b6f20c6a5748151c6d79f1`,
`crates/infer/src/constraints/row_effect.rs::constrain_effect_family_by_filter`
and `effect_family_passes_filter` create `FilterInvariant` constraints before
the filter check is consumed. `collect_neg_effect_items` creates
`PayloadInvariant` constraints against the first same-path item, then drops
each duplicate from the collected row. `intersect_row_items_with_left_stack`
routes through `common_stack_subtractability`, which constrains duplicate
families in stack entries before intersecting them; `machine/propagate.rs`
does the corresponding common-stack check for an upper `Neg::Stack` before
continuing through its inner endpoint. `subtract_row_items_from_left_stack_weight`
and `subtract_effect_families` create transformation constraints while
rewriting pushed filters against removed families. The shared helper
`enqueue_row_invariant_args` currently expands each zipped argument pair into
two polarized subtype constraints.

This locates when those frozen paths create constraints and where row items or
filters are subsequently discarded. It does not prove that the Oracle's
pairwise rules, representative-star duplicate collection, or weighted route
are sound/principal, and it does not supply the successor's `Demand` relation.
For the successor, the useful obligation is temporal: derive a stable symbolic
key and attach it to every dependent view before the corresponding semantic
operation consumes, collapses, or moves its typed occurrence. The applicable
source rules must still decide which pairs create keys; this crosswalk cannot
promote every same-head encounter into a rule.

The shorthand `InvArgs(F<τ̄>,F<ῡ>) = ⋀ᵢ(τᵢ <: υᵢ ∧ υᵢ <: τᵢ)` is a
candidate symbolic encoding, not a statement copied literally from the frozen
specs. The frozen effect spec asks for invariant ordinary constraints, while
the invariant-type sandwich spec can represent invariant arguments as
lower/upper intervals or lifted concrete bounds; interval merges generate
cross-bound obligations. A successor must define `τ <: υ` for its actual
type-term representation and prove that this shorthand denotes the required
invariant relation, including interval-valued arguments. Until then,
preserving the symbolic formula is necessary for the candidate relation but
does not by itself establish Oracle-equivalent argument invariance.

#### Overlap is not mutual subtyping for interval arguments

The frozen invariant-type sandwich spec distinguishes a bounded argument
from a concrete type term. An interval `[L,U]` describes the arguments admitted
by its lower and upper constraints; coalescing two occurrences as one
invariant argument requires a common witness satisfying both intervals. For
intervals `A=[L_A,U_A]` and `B=[L_B,U_B]`, the endpoint condition is

```text
for every l in L_A ∪ L_B and u in U_A ∪ U_B: l <: u
```

This is the condition in the frozen spec's cross-bound generation (with each
interval's own feasibility retained). It is not equivalent to mutual subtype
of the two interval descriptions when those descriptions denote sets of
admissible concrete arguments. In a four-element chain
`0 <: 1 <: 2 <: 3`, let `A=[0,2]` and `B=[1,3]`. Their intersection is
nonempty (`1` and `2` are common witnesses), and all cross-bound inequalities
hold. But the admissible sets differ, so neither interval denotes a subtype of
the other by set inclusion; mutual subtyping rejects this valid shared-
argument case. Conversely, treating the two endpoint pairs as point types
would confuse the interval constraints with concrete values.

Thus the candidate `InvArgs` name must not silently mean mutual subtyping of
interval objects. The successor needs a symbolic *common-witness / interval
intersection* relation for interval-valued invariant arguments, with a
separate pointwise equality relation only for already concrete argument
values. Its solver encoding must retain the lower/upper endpoint ownership and
all cross-bound obligations through solving, residualization, generalization,
fresh instantiation, and intrusion. The finite-join lemma below supplies
common-witness existence only conditionally; it does not justify replacing
the symbolic relation with its current finite consequences or choosing the
carrier. This is a specification distinction and proof obligation, not a
change to the frozen spec or a selected successor rule.

#### Naive outer-endpoint flattening loses nested invariant overlap

The overlap relation cannot be implemented *exactly* by turning every
compound bound into its lifted lower and upper outer types and then applying
the endpoint theorem. Consider a three-element chain `0 <: 1 <: 2` and a
unary constructor `C` with invariant subtyping:

```text
C(a) <: C(b)  iff  a = b
```

Under the recursive lifted-bound interpretation, `C([0,2])` admits the
shape-locked values `C(0)`, `C(1)`, and `C(2)`. Two occurrences
`C([0,1])` and `C([1,2])` share `C(1)`. But flattening their bounds to outer
interval endpoints and requiring `C(0) <: x <: C(2)` fails immediately:
invariance gives `C(0) </: C(2)`, even though the nested argument intervals
overlap. Thus endpoint overlap must be computed at the invariant argument
position while retaining the constructor path and its variance; whole-term
mutual subtyping or this naive outer-endpoint interval is not an exact
replacement. A more permissive outer interval could over-approximate these
admissible sets; this example does not rule out every possible interval
encoding, but such an encoding would need its own exactness/principality proof.

This is a conditional counterexample for the stated recursive-bound meaning
and invariant constructor rule. The frozen sandwich spec's lifted
`CompactBounds::Con` shape is characterization evidence for retaining
constructor structure, not semantic authority for the successor. The
successor still needs a structural admissible-value relation for lifted
`Con`, `Tuple`, and `Fun` bounds, with variance-specific witness conditions
proved sound and complete against its selected type domain. Every nested
endpoint and constructor-path incidence must remain symbolic through the
same solve/residualize/generalize/freshen/intrude lifecycle. The N-way
endpoint theorem applies only after such a sound decomposition has produced
the argument-position endpoint sets.

#### Conditional structural overlap in the tagged powerset carrier

There is a candidate structural meaning for a finite acyclic lifted bound,
but only inside the unselected tagged powerset carrier described in
`notes/progress/2026-09-30-intrusion-powerset-carrier-candidate.md`. Let
`D = P(N)` with subset order and fix one assignment `η` for all type
identities in the endpoint expressions. Define the denotation of an interval
leaf by

```text
[[Interval(L,U)]]η = { t ∈ D | (∀l∈L. lη ⊆ t) ∧ (∀u∈U. t ⊆ uη) }
```

For a lifted node with one known head `K`, define

```text
[[K(B₁,…,Bₙ)]]η = { Enc_K(t₁,…,tₙ) |
                     tᵢ ∈ [[Bᵢ]]η for each i }
```

Here `K` is a well-kinded nominal constructor with its declared variance, or
a pure Function, using the candidate's disjoint, injective variance channels.
Tuple/product heads are excluded because the powerset candidate has no product
encoding. The lifted-bound denotation is intentionally a set of candidate
type values; it is not defined as the interval between one flattened pair of
outer types.

For two interval leaves with finite endpoint sets, intersection is nonempty
exactly when every lower endpoint from either leaf is below every upper
endpoint from either leaf. The powerset witness is the union of all lower
endpoints. For two lifted nodes with the same head and independent child
slots, injectivity and disjointness of `Enc_K` make their denotations overlap
exactly when each pair of corresponding child denotations overlaps. Different
lifted heads have disjoint images. Induction gives this result for finite
acyclic trees whose comparison is aligned at each node as Interval/Interval
or same-head Lifted/Lifted.

This structural factorization does not itself cover an Interval/Lifted
comparison; a conditional membership rule follows below. It does not cover
tuple/product, record, or effect heads because the candidate has no encoding
for them. It also does not factor child checks when slot witnesses have
cross-slot identity constraints. In that case the condition is one existential
choice of `η` and all child witnesses satisfying the complete
incidence/constraint graph together; separate per-slot existentials can change
the solution set. Recursive or polarity-reversing bounds, effectful Function
slots, source-rule obligation generation, and root/use observations are
outside this lemma. It is conditional evidence
that retaining a variance-tagged structural graph can express nested overlap
in this carrier, not proof that this carrier is selected, source-adequate,
principal, or suitable for implementation. The type/evidence incidence
required by the user remains symbolic through every phase.

#### Mixed interval/lifted membership rule (conditional)

For the same candidate carrier, an Interval/Lifted comparison can be reduced
recursively when child slots are independent. Let an interval leaf have finite
lower endpoint list `L` and upper endpoint list `U`, evaluated under fixed
`η`, and write

```text
L₀ = ⋃ { lη | l ∈ L }       U₀ = ⋂ { uη | u ∈ U }
```

with empty union `∅` and empty intersection `N`. For a lifted head `K`, let
`H_K` be its unique head atom, `S_K` its head plus all of its used channel
ranges, and `decode_c(X) = { n | pair(c,n) ∈ X }`. A candidate
`Enc_K(t₁,…,tₙ)` lies in the interval exactly when

```text
L₀ ⊆ S_K,   H_K ⊆ U₀,
L_c ⊆ g_c(tᵢ),   and   g_c(tᵢ) ⊆ U_c   for each used channel c of slot i,
```

where `L_c = decode_c(L₀)`, `U_c = decode_c(U₀)`, and `g_c` is the encoding
payload (`tᵢ` for a positive/covariant channel, `N \ tᵢ` for a
negative/contravariant channel). A missing support or head condition makes
membership impossible. For a positive channel the child gains lower/upper
bounds `L_c ⊆ tᵢ ⊆ U_c`. For a negative channel the inequalities reverse
under complement, giving `N \ U_c ⊆ tᵢ ⊆ N \ L_c`. An invariant slot
combines its positive and negative channel bounds by unioning the resulting
lowers and intersecting the uppers. Thus the child comparison is recursively
between `Bᵢ` and an interval leaf over these derived carrier endpoints.

Induction on the finite lifted tree gives an exact recursive characterization
of membership for Interval/Lifted pairs, and therefore a semantic overlap
relation by applying the derived child constraints to the lifted children.
This structural recursion terminates, but the relation still uses inclusion
tests over arbitrary elements of `P(N)`. No effective representation or
terminating inclusion oracle for those subsets has been supplied, so this is
not a decision procedure or solver algorithm. It is a semantic calculation
in `P(N)`, not a claim that generated endpoint subsets have finite source
expressions or can be inserted into a solver graph. It assumes fixed endpoint
values, the exact tagged-channel encoding above, and independent child
witnesses. Shared slot identities or jointly existential graph variables
require one coupled incidence relation and cannot be tested by separate child
recursion. The powerset carrier, channel scheme, and this membership rule all
remain unselected pending a whole-envelope soundness and principality proof.

#### Effective regular-tree subcarrier (candidate)

The previous calculation ranges over arbitrary subsets of `N`, so it has no
effective subset representation by itself. A possible effective restriction
is `RegΣ(N)`, the regular tree languages over one fixed finite ranked
signature `Σ` for a compilation unit. Use the same atom and unary channel
constructors as the tagged encoding, with `N` the set of all finite `Σ`-trees
and the order still language inclusion. This is a candidate carrier
refinement, not a selected successor decision.

Assume every endpoint evaluated under `η`, including each nested and
generated child endpoint, is supplied as a finite tree automaton or can be
constructed effectively from source endpoint syntax. Under that input
presentation, all operations used above stay regular: finite union and
intersection, complement relative to `N`, singleton head atoms,
channel-prefix images, and channel decoding. Inclusion is decidable by
testing emptiness of the regular difference `A ∖ B`. Thus `RegΣ(N)` has
bottom `∅`, top `N`, and finite joins given by language union. The interval
common-witness test is decidable: combine lower endpoints by union, upper
endpoints by intersection, and test inclusion. The mixed Interval/Lifted
transform also produces regular endpoint languages and uses only those
operations. For finite acyclic structural bounds with independent child
slots, the recursive semantic characterization therefore becomes an
effective decision procedure in this subcarrier.

Constructor encoding preserves regularity because each used variance
channel is a unary context image; contravariant channels additionally take
regular complement. The finite alphabet assumption matters: the relevant
constructors, variance channels, and atom codes must be fixed for the whole
compilation unit. This does not prove that every satisfying SCC assignment is
regular, that regular assignments preserve the intended source typing
relation, or that a principal root/use scheme is representable by finite
automata. Recursive/polarity-reversing constraints, shared identity
incidence, effect rows and effectful Function slots, width-subtyped records,
method selection, and Oracle final-acceptance adequacy remain unproved. A
conditional uniform encoding for exact-head fixed-variance constructors,
including fixed-arity covariant tuples, is given immediately below; its
source adequacy and complete root/use preservation remain open. In particular,
the regular-tree restriction may lose a source solution that requires a
non-regular language; that cannot be excluded from this local closure
argument. Keep all symbolic family constraints and owner edges in the graph
until those adequacy and principality obligations are closed.

#### One encoding for exact-head variance constructors

The tagged carrier has a uniform extension to any finite-arity exact-head
constructor whose source subtype rule is componentwise by a fixed variance
vector. Give constructor `K` a unique head atom `h_K`, and give each slot `i`
two disjoint unary channel tags `p_{K,i}` and `n_{K,i}`, all disjoint from
every other head and channel. For child denotations `X_i ⊆ N`, define

```text
Enc_K(X₁,…,Xₙ) = {h_K}
  ∪ ⋃_{i covariant} p_{K,i}(X_i)
  ∪ ⋃_{i contravariant} n_{K,i}(N \\ X_i)
  ∪ ⋃_{i invariant} (p_{K,i}(X_i) ∪ n_{K,i}(N \\ X_i))
```

where a channel maps a language to the language of trees prefixed by that
channel tag. Unique heads make inclusion between different constructors
impossible. For the same head, disjoint channels reduce inclusion exactly to
`X_i ⊆ Y_i` on covariant slots, `Y_i ⊆ X_i` on contravariant slots, and
`X_i = Y_i` on invariant slots; the latter follows from the two opposite
channel inclusions. Thus ordinary structural variance is one encoding lemma,
not a separate semantic carrier per type constructor.

When endpoint languages are regular, finite channel-prefix images, relative
complements, and unions remain regular. A tuple constructor with exact arity
and covariant element subtyping is one instance of this encoding; tuple arity
is distinguished by the unique head. This extension applies to the finite
regular-witness argument when the constructor's ranked symbols are included
in the fixed signature. It is conditional on the actual source rule having
that exact-head variance form. It does not cover width-subtyped records,
dependent/shared slots, or Function effect rows, and it does not prove that
the regular restriction preserves complete root/use fibers. The channel tags
are a denotational encoding choice, not source-level selectors.

The frozen behavior premise is recorded in
[`2026-09-29-intrusion-abstract-semantics-draft.md`](2026-09-29-intrusion-abstract-semantics-draft.md),
§ “Full-envelope stage boundary.” For closed ground tuples, this constructor
lemma gives a concrete final-acceptance comparison point. At equal arity,
inclusion reduces to the componentwise covariant obligations that the frozen
Oracle emits. At unequal
arity, distinct head atoms make inclusion fail. The Oracle can defer that
shape failure until concrete specialization, but its final specialization
rejects the mismatch. Thus this candidate may reject earlier while preserving
the observed final result for this closed-ground case; the phase difference
is within the user's explicit compatibility allowance. This does not establish
parity for open tuple variables, optional/width record fields, or tuples
nested inside effects or recursive bounds.

#### Regular-witness property for finite pure constraints (candidate theorem)

The carrier refinement has a stronger conditional property for the finite
pure fragment. Fix a finite ranked signature `Σ` using exactly the disjoint
atom and unary-channel tags of the tagged encoding; symbols outside a
constructor's assigned head/channel tags contribute no membership in that
constructor. Fix finitely many type variables
`V`, and a finite set of subtype constraints `e ≤ f`. Require every endpoint
to be a finite expression over variables, `Bottom`, `Top`, finite union and
intersection, and the exact-head variance constructors above. If
there is any satisfying assignment `ν : V → P(N)`, then there is also a
satisfying assignment `ν_reg : V → RegΣ(N)`. The variable constraint graph
may contain arbitrary finite cycles; no acyclicity premise is used.

Proof. Let `E` be the finite set of all endpoint subexpressions. At each tree
`t ∈ N`, form a finite state containing (i) one bit for membership of `t` in
each `ν(X)`, `X ∈ V`, and (ii) one bit for membership of `t` in the denotation
of every `e ∈ E`. The resulting state set `Q` is finite. For each ranked
symbol, constructor membership is determined locally from its assigned
head/channel tag and child-subexpression bits; symbols with another tag yield
false for that constructor. Union/intersection and complement are
Boolean operations on the corresponding bits. Retain only transitions whose
subexpression bits obey these local rules and whose state satisfies every
constraint `e ≤ f` at the current tree. The arbitrary satisfying `ν` induces
a valid state at every tree, so let `Q₀ ⊆ Q` be the finite set of states it
uses. For any symbol and tuple of child states from `Q₀`, choose representative
child trees carrying those states and compose them into a tree. The state of
that tree under `ν` supplies a valid successor state in `Q₀`. Choose one such
successor for each tuple; nullary symbols use their state under `ν`. This
finite transition table defines a bottom-up tree automaton. By induction on
tree height, its states satisfy every local constraint. The variable-membership
bits therefore define regular languages `ν_reg(X)` satisfying all original
subtype inclusions. A finite regular outer environment can be added by
carrying its supplied automaton states in the product state and constraining
the corresponding identity bits to match.

Let `m = |V| + |E|`, so `|Q| ≤ 2^m`. Enumerate deterministic bottom-up
transition tables over this fixed state universe. For a symbol `s` of rank
`r`, a total table has at most `|Q|^(|Q|^r)` choices; over finite `Σ`, the
number of tables is finite. For each table, compute the reachable states by
least closure from the nullary transitions. Check the local subexpression
equations on each reachable transition and check every edge `e ≤ f` on every
reachable state. The bit for each `X ∈ V` then defines its recognized regular
language. If outer anchors are fixed regular automata, take their automaton
state product with `Q`; the same finite enumeration and closure check applies
over that product state universe. The representative-tree construction in the
existence proof supplies one valid table whenever an arbitrary powerset model
exists, so this is a finite decision procedure for the stated constraint
fragment. Its state bound is at most `2^m` before the outer-anchor product;
the transition-table search is enormous, and no practical optimization or
implementation is established here. The result says that restricting this
carrier to regular languages loses no **existence of a satisfying assignment**
for these finite constraints, including cyclic subtype SCCs. It does not
establish guarded/productive recursive Function semantics, preserve every
arbitrary assignment, the joint root/use solution relation, principality, or
the exact source acceptance judgment. It includes exact-head products such as
fixed-arity covariant tuples only when their source subtype rule meets the
preceding encoding premise. It excludes width-subtyped records, effects, methods,
non-regular fixed anchors, and any constraint form not expressible by the
finite local endpoint grammar. SCC intrusion and the required symbolic
family-constraint lifecycle remain separate proof obligations.

The distinction between model existence and fiber preservation has a direct
counterexample. Let `Σ` contain unary symbols `a,b` and a nullary symbol `z`,
and let `L = { aⁿ(bⁿ(z)) | n ≥ 0 }`, which is not a regular tree language
(its unary-tree restriction is the nonregular word language `{aⁿbⁿ}`). With
one unconstrained observable root variable `x`, the powerset constraint
relation admits `x=L`; the regular subcarrier does not. Therefore regular
model existence cannot justify replacing the complete powerset root/use
fiber by its regular assignments. Such a carrier can be principal only
relative to a source expressibility theorem showing that source-observable
type values are regular, or to an observation equivalence that provably
identifies every lost assignment with a retained one. Neither premise is
established for Yulang SCC roots.

#### Conditional bridge from finite source types to the regular carrier

The nonregular-root example rules out silently replacing the full
`P(N)` observation fiber. It does not by itself rule out `RegΣ(N)` as the
successor's type-value carrier, because source clients may only express finite
type terms. For the finite fragment generated by atoms, `Bottom`, `Top`, union,
intersection, and the exact-head fixed-variance constructors above, every
finite term denotes a regular language: atoms are finite languages; `Bottom`
and `Top` denote `∅` and `N`; union/intersection preserve regularity; and each
constructor uses only finite channel images and relative complement. The same
induction applies when type variables are assigned regular languages. This is
a direct closure proof, conditional on the source elaboration using only this
finite constructor grammar and a fixed finite signature.

Now take a finite constraint system in the regular-witness grammar with fixed
regular outer anchors. Since `RegΣ(N) ⊆ P(N)`, every regular solution is a
powerset solution. The regular-model theorem gives the converse on
satisfiability: if any powerset solution exists, a regular solution exists.
Thus the two carriers agree on **existence** for each such finite constraint
system, including cyclic subtype SCCs and the joint interval-family encoding.
If source elaboration for a pure input envelope is exact into this constraint
grammar, this establishes a conditional final-acceptance bridge for that
envelope even though the arbitrary assignment fiber differs. The source
elaboration equivalence, complete root/use principality, and the method for
presenting regular solutions as successor interfaces remain unproved; no
claim is made for records, effects, methods, or recursive Function semantics.

The current syntax-v0 pages give a concrete source-form checklist for this
bridge, but they define grammar rather than typing or denotation
(`syntax-reference/en/src/types/type-expression-core.md` and its composed
construct pages):

| Source form | Candidate regular-carrier mapping | Still required for an Oracle envelope |
| --- | --- | --- |
| Resolved primitive/type-variable atom | Finite head atom or a constraint variable | Prove name resolution and the selected base subtype order match the source type relation. |
| Type call/application | Exact-head constructor with its declared finite variance vector | Prove every admitted declaration elaborates to that constructor relation; aliases and nominal-cast outcomes need their own source mapping. |
| Equal-arity tuple-like type | Exact-head tuple constructor with covariant element channels | Source characterization supports this rule; prove lowering and final public outcomes through SCC/use contexts. |
| Unequal-arity tuple pair | Different heads, hence no subtype inclusion | Oracle defers this mismatch to specialization; the closed-ground final rejection is characterized above, but open-variable interactions remain open. |
| Pure Function type | One exact-head constructor with contravariant argument and covariant result | Requires a source proof that all latent effect views are empty and that no pure-argument-effect side rule adds constraints. |
| Effectful Function, named record, `forall`, effect row, polymorphic variant, bracket row | Not in the current finite pure carrier grammar | Their semantics and final acceptance must be added before claiming Oracle-capable full-envelope support. |

This is a candidate partition, not a selected source envelope. The syntax
pages do not establish any row in the semantic column. The regular-model
bridge becomes a final-acceptance theorem only after lowering and every
relevant inference/specialization judgment are proved equivalent to the
finite constraint grammar for the included forms.

#### Regular-model extension for joint interval family batches

The regular-witness theorem applies to a finite collection of already
source-derived interval-valued `InvArgs` batches in this pure fragment. Put
every shared argument identity `w_i` from every batch in the same finite
variable set as the roots and endpoint variables. For each occurrence owner
`o` constraining `w_i`, with finite endpoint sets `L_{o,i},U_{o,i}`, add

```text
l ≤ w_i    for each l ∈ L_{o,i}
w_i ≤ u    for each u ∈ U_{o,i}
```

Retain each `w_i` and its batch/owner incidence; do not replace it with a
materialized join or merge different source batches. Include any other
cross-position or root-coupling subtype constraints in the same finite graph.
If the resulting graph has a solution in `P(N)`, the regular-witness theorem
gives one joint solution in `RegΣ(N)` for all its variables, including all
the shared `w_i`. Thus identities and correlations already expressed by the
finite subtype graph are solved together; no independent-per-position witness
choice is made. Fixed outer anchors are covered only when their supplied
denotations are regular, as required by the finite-regular-environment
premise.

This is a regular-model existence result for the finite subtype presentation,
not preservation of each arbitrary solution or its complete root/use
observation fiber. It does not derive which source occurrences share a
binder, encode a cross-position relation that is not expressible as finite
subtype constraints, cover open effect tails, or prove principal SCC
intrusion. It strengthens the pure satisfiability fragment without
discharging the symbolic lifecycle invariant: every `w_i`, batch key, and
owner edge still must travel through solving, residualization,
generalization, use freshening, and intrusion.

#### Variable-edge propagation into interval constraints (conditional)

This identifies one solver expansion of the `InvArgs` shorthand; it does not
prove that the expansion is complete for common-type existence. Let `x` and
`y` be type variables with finite, transitively saturated lower endpoint sets
`Lₓ`, `Lᵧ` and upper endpoint sets `Uₓ`, `Uᵧ`. Assume each current interval is
feasible, all variable-alias paths affecting these endpoints are already
included in the saturation, and ordinary subtype satisfaction is evaluated
in a fixed preorder. Add the symbolic obligations

```text
x <: y
y <: x
```

Both edge obligations remain part of the constraint graph. After saturating
the variable-bound propagation, the endpoint sets are:

```text
L'ₓ = L'ᵧ = Lₓ ∪ Lᵧ
U'ₓ = U'ᵧ = Uₓ ∪ Uᵧ
```

Each variable edge propagates the lower endpoints of its source to its target
and the upper endpoints of its target to its source. Together the two edges
give both variables the union of their lower demands and the union of their
upper demands. Saturating the resulting bounds emits cross constraints
`lₓ <: uᵧ` for `lₓ ∈ Lₓ, uᵧ ∈ Uᵧ` and `lᵧ <: uₓ` for
`lᵧ ∈ Lᵧ, uₓ ∈ Uₓ`, in addition to the within-interval obligations already
present. Every valuation satisfying both intervals and both mutual-subtype
edges satisfies these cross constraints by transitivity. This is the
necessary cross-bound generation described by the invariant-type sandwich
spec.

The converse, that these pairwise endpoint constraints guarantee a common
argument witness, does not follow from an arbitrary preorder. For example,
take a four-element partial order with incomparable `a,b` below incomparable
`u,w`, with `a <: u`, `a <: w`, `b <: u`, and `b <: w`, but no common element
between both lower and both upper endpoints. Intervals `[a,u]` and `[b,w]`
are each feasible and every cross constraint holds, yet they have no common
witness. Sufficiency therefore needs a finite interval-realization property
proved for the successor's type domain; it is not supplied by this propagation
lemma or the frozen sandwich spec.

The symbolic edges remain necessary when `x` and `y` have distinct root or
use observations. Replacing them with only the merged interval would need a
separate quotient proof that preserves those observations. The generated
endpoint constraints are solver consequences, not permission to erase their
symbolic source.

#### Finite-join condition that makes the interval witness exist

The missing converse does hold under a concrete carrier property. Let `(D,≤)`
have a least element `⊥` and joins of all finite subsets satisfying the
least-upper-bound laws. For finite endpoint sets `L,U ⊆ D`, the following are
equivalent:

```text
for every l ∈ L and u ∈ U, l ≤ u
there exists t ∈ D such that every l ∈ L satisfies l ≤ t
                         and every u ∈ U satisfies t ≤ u
```

For the forward direction choose `t = ⋁L`, using `⊥` when `L` is empty. Each
lower endpoint is below `t`; for each `u ∈ U`, every `l ∈ L` is below `u`, so
the least-upper-bound law gives `t ≤ u`. For the reverse direction, compose
`l ≤ t` and `t ≤ u`. Thus the arbitrary-preorder counterexample above is
excluded if the successor's actual value carrier has these finite joins.

This proves common-witness existence for the endpoint fragment only. It does
not establish that the successor's recursive/structural type domain is closed
under these joins, that the generated term is representable within its
supported envelope, or that replacing two symbolic roots by that witness
preserves their joint observations. The finite-join carrier remains an
unselected candidate assumption; the actual type-domain realization proof is
still open.

The least-element premise is stronger than needed whenever the batch has at
least one lower endpoint. For finite nonempty `L`, finite joins alone give the
same proof with `t = ⋁L`; pairwise `l ≤ u` implies `t ≤ u` for each upper
endpoint. If `L = ∅`, the pairwise condition is vacuous and cannot by itself
guarantee a witness: the exact remaining requirement is that `U` have a
common lower bound (with nonempty `D` needed when `U` is empty). Thus a
uniform carrier condition for all finite endpoint sets can be stated as
finite nonempty joins plus common lower bounds for finite upper sets; a least
element is one simple sufficient way to satisfy the latter. This separates
the join property that realizes constrained lower endpoints from the bottom
assumption needed only for unconstrained lower sides. It still does not show
that the Yulang type carrier has either property.

#### N-way typed-family argument overlap (carrier-parametric)

The endpoint result extends to any finite batch of occurrences that one
source-derived rule requires to denote the same invariant family argument;
it does not impose a relation on every same-head occurrence in a program.
Fix such a batch of `k ≥ 1` occurrences of family head `F` with arity `m`.
For each argument position `i`, let `Lᵢ` be the union of all lower endpoints
and `Uᵢ` the union of all upper endpoints contributed by the batch's
occurrence-owned argument intervals at that position. Assume each occurrence's
interval contributes finite lower and upper endpoint sets, already derived by
a semantics-preserving decomposition of its argument bounds; therefore the
batch unions `Lᵢ` and `Uᵢ` are finite. Also assume the endpoint carrier `D`
has a least element and all finite joins satisfying the least-upper-bound
laws, or more generally has the finite interval-realization property from
the preceding lemma. Under these premises, one shared tuple of argument
witnesses exists in the independent per-position endpoint fragment exactly
when

```text
for each i ∈ 1..m, for every l ∈ Lᵢ and u ∈ Uᵢ: l ≤ u
```

Necessity follows by composing every `l ≤ tᵢ` and `tᵢ ≤ u` through the
shared witness `tᵢ`. For sufficiency under the stated join assumption, choose
`tᵢ = ⋁Lᵢ` (or `⊥` for an empty `Lᵢ`); the LUB law gives `tᵢ ≤ u` for every
`u ∈ Uᵢ`. A nullary family has no argument obligations and the condition is
vacuous. This gives an order-independent N-way common-witness criterion for
the source-derived batch in the already decomposed endpoint fragment and
avoids unsoundly demanding mutual subtyping between interval descriptions.

This result does not establish that compound `Con`, `Tuple`, or `Fun` bounds
decompose into independent per-position endpoint sets; that requires the
chosen type-domain semantics and its variance/equality rules. It also does not
cover cross-position correlations caused by shared type variables: those
remain in the joint symbolic constraint graph, and per-position feasibility
cannot replace solving that graph. No current successor carrier has been
shown to satisfy the join premise. The occurrence-owned endpoint sets and
their incidence with every `InvArgs` demand must remain symbolic through
solving, residualization, generalization, fresh instantiation, and intrusion.
This is a conditional lemma, not a selected successor relation or permission
to materialize a witness and discard its source constraints.

This does not prove the equivalence for arbitrary compound arguments,
non-saturated recursive graphs, effect weights, or post-substitution
residuals. Those require the structural subtype decomposition and fixed-point
solver to preserve the relation and all endpoint ownership. In particular,
the result does not authorize replacing the symbolic formula with its current
finite set of cross-bound consequences before later graph changes have been
accounted for.

#### Symbolic batch formula for interval-valued family arguments (conditional)

The endpoint theorem gives a concrete formula for the interval-leaf case of
the family-argument obligation. Let `B` be one finite batch of occurrences
that a source rule independently requires to share one invariant argument at
position `i`; `B` is not inferred from all same-head occurrences. Each owner
`o ∈ B` contributes a symbolic interval `[L_o,U_o]` with finite endpoint
sets. Define the keyed obligation:

```text
MeetKey(B,i) = (source_site, stable_batch_id, family, argument_position,
                occurrence_owner_ids(B))
MeetFormula(B,i) = { l <: u | l ∈ ⋃_{o∈B} L_o,
                              u ∈ ⋃_{o∈B} U_o }
```

The endpoint expressions are transported payload, not part of the stable key.
Substitution may change or identify their formula text, but it does not merge
distinct batch/owner identities; existing records are reconciled by the
transported stable key while preserving proof state and owner paths.

Assume all endpoint expressions are interpreted under one joint assignment
`ν`, each interval is feasible in the selected type preorder, and that
carrier has a least element and all finite joins (or the equivalent finite
interval-realization property). Then `MeetFormula(B,i)` is satisfiable under
`ν` exactly when one concrete argument value satisfies every interval in
`B`. If the formulas hold, choose the join of the union of lowers as the
shared witness; each upper endpoint bounds that join by the least-upper-bound
property. Conversely, any shared witness composes every lower-to-witness and
witness-to-upper inequality. For a family with several independent argument
positions, apply this formula at each position under the same `ν`. It does not
permit independent assignments to shared variables or model additional
cross-position witness correlations.

The symbolic record is the batch key plus its endpoint expressions, not a
materialized join witness. The required phase contract is: solving substitutes
the endpoints uniformly; residualization transfers the key and its owner
paths to every still-demanded view; generalization binds the locally owned
endpoint identities together with the family rows; fresh instantiation maps
all endpoints and occurrence owners in one use-local map; intrusion transports
endpoints through `P` and incidence through `M`. Under injective
capture-avoiding maps, the formula is alpha-transported and satisfaction is
preserved by assignment reindexing. If a solver derives the current
cross-bound inequalities, it retains the batch key and proof/equivalence
evidence while a dependent view remains live; it does not reconstruct the
batch from concrete rows or discard occurrence ownership merely because some
endpoint formulas become equal. These are required transition properties,
not claims that an actual solver has proved them.

This supplies a symbolic interval-leaf candidate in place of mutual subtype
between interval descriptions, which rejects valid overlaps such as `[0,2]`
and `[1,3]`. It does not define common witnesses for compound `Con`, `Tuple`,
or `Fun` arguments, establish that the chosen successor type domain has the
assumed joins, or prove which source rules form each batch. It is a conditional
local formula plus transport obligation, not a selected row semantics or an
actual solver correctness theorem. The existing `InvArgs` notation remains a
shorthand only where its endpoint terms denote point types or another proved
equivalent relation.

#### Representative-star merge is not an N-way interval meet (Oracle characterization)

The frozen Oracle source has a concrete representative-star pattern in
`crates/infer/src/constraints/row_effect.rs` at commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1`. In
`collect_neg_effect_items`, the first item for a family path is retained;
each later duplicate calls `enqueue_row_invariant_args(existing_args,
args)` against that first argument vector, then is discarded from the row
item list. `enqueue_row_invariant_args` zips argument positions and emits the
two polarized subtype obligations for each pair. This is a source-code
characterization of this collector, not a claim that weight routing is
semantically sound or that every source program reaches this input.

For interval-valued arguments, the directly emitted representative-star
pairwise formulas are weaker than the formula for one common witness across
all duplicates. Use the chain
`Never <: Int <: Any` and three feasible intervals:

```text
A = [Never, Int]
B = [Int, Any]
C = [Never, Never]
```

The star comparisons `A` with `B` and `A` with `C` each have a witness
(`Int` and `Never`, respectively), so their pairwise cross-bound formulas
hold. No value satisfies all three: `B` requires `Int <: t`, while `C`
requires `t <: Never`, which would imply the false `Int <: Never`. Therefore,
if duplicate collection's source meaning is that all same-path items share
one argument, comparing every duplicate only with the first does not prove
that meaning. The whole-batch `MeetKey` formula must combine endpoints from
all occurrences, or preserve a relation whose denotation does so.

The effect-subtraction specification lists duplicate row-head collection as
an invariant site, and the frozen sandwich design says same-slot merges need
cross-bound constraints. These are characterization evidence for the
common-witness interpretation, not authority for the successor's complete
effect semantics. The algebraic counterexample proves a mismatch between
representative-star constraints and N-way common-witness semantics; it does
not yet prove that a well-typed Yulang source program can produce exactly
these three interval arguments or that frozen `check` accepts that program.
Do not record a final Oracle compatibility exception until that reachable
source case is constructed and observed. If reachable, the successor should
prefer the sound whole-batch condition and record the concrete final-acceptance
difference before treating the Oracle result as unsupported behavior.

#### Frozen source acceptance witness for duplicate typed-family collapse

A bounded source probe now reaches a related final Oracle observation. The
temporary source is:

```yulang
pub act ask 'a:
  pub get: () -> 'a

pub dup(f: () -> [ask int, ask _, ask never] ()) = f()
```

At frozen commit `a58eefc31e22141574b6f20c6a5748151c6d79f1`,
`yulang --no-prelude --no-cache check` accepts this source with exit status 0
and no diagnostics. `dump --poly-raw` for `dup` gives the callback effect as
one `ask` item whose argument is `Bounds(int, Bot)`. Under the recorded
candidate carrier where `Never` is bottom and `int` is not a subtype of
`Never`, this interval has no inhabitant. The source therefore supplies a
concrete final-acceptance observation involving three duplicate same-family
items and a collapsed empty argument interval.

This does not yet establish that weighted
`collect_neg_effect_items` at `row_effect.rs:1064` is the pass that collapses
these particular annotated items: the CLI exposes no phase trace, and that
collector's invocation depends on nonempty weights. Nor does source acceptance
alone decide whether the annotation denotes a required common typed argument;
that is a successor semantic obligation. Keep symbolic `InvArgs`/batch
evidence alive through solving, residualization, generalization, freshening,
and intrusion. Do not rebuild it from this already-collapsed `Bounds(int,
Bot)` row. If the reviewed successor relation requires one common inhabited
argument, it would reject this source, so the eventual compatibility impact
would be that Oracle-accepted annotation; record that divergence only after
the full weighted route and successor source meaning are established. This is
not yet the N-way interval witness from the previous subsection: source syntax
here supplies fixed `int`, wildcard, and `never` arguments, not the abstract
intervals `A`, `B`, and `C`.

Let an operation declaration at exact path `p` have signature
`op : A -> [E] B` and declaration binders `ā`. Resolving one source request
allocates one capture-avoiding map `θ` for those binders. Declaration
elaboration must also supply the associated family identity `F` and its
family-argument expression tuple `ρ̄`, under explicit ownership; `ρ̄` is not
assumed to be the full binder list `ā`, and its terms may be compound
expressions. The map `θ` applies consistently to every owned occurrence in
`A`, `B`, `E`, and `ρ̄`. If the language derives `ρ̄` from `E`, that projection
must be part of the declaration rule and proved to preserve binder ownership.
The request view is:

```text
Request(p, q, θ) =
  (OpId(p), FamInst(F<ρ̄θ>), payload : Aθ,
   result : Bθ, latent : Eθ, source_origin, use_occurrence)
```

The request typing premises constrain its payload against `Aθ`, its result
against `Bθ`, and retain `Eθ` pending a source-defined owner/route rule.
Operation-only binders remain in the shared signature map even when they do
not occur in `ρ̄`. The family instance is typed data; its projection to
`FamHead(F)` is only support. The
exact `OpId(p)` remains the operation identity used by handler selection.

For any candidate source rule that relates two typed row items with the same
family head, write them as
`FamInst(F<χ̄>)@o₁` and `FamInst(F<ῡ>)@o₂`; `o₁` and `o₂` retain the distinct
source/use owners of the two row occurrences. For each argument position `i`,
the rule derives a stable obligation key before changing either structure:

```text
oᵢ = (relation_site, left_origin/use, right_origin/use, F, i,
     view_occurrence_id)
Formula(oᵢ) = (χᵢ <: υᵢ  and  υᵢ <: χᵢ)
```

The argument terms `χᵢ` and `υᵢ` are symbolic formula payload, not key
identity. Type substitution updates the payload in place; the use/view
occurrence map transports `view_occurrence_id` during freshening or intrusion.
This keeps source-pair incidence stable while endpoint terms change.

In the source that generates the relation, `χ̄` and `ῡ` are obtained by
projecting the family arguments from the two row items, not from all operation
scheme binders. The frozen spec directly characterizes invariant constraints
for row split, residual subtraction, duplicate-head collection, filter
check, and common-stack check. Other cases below are candidate successor
rules and require their own typing proof.

For a callback/function argument comparison, the candidate source rule
compares the actual and formal latent rows as typed row views. If both contain
the same family head, it emits each `Formula(oᵢ)` for their two independently
owned family arguments before row projection or residualization. This is a
new source rule; neither the frozen row-set spec nor runtime path matching
proves it. For an operation arm matching `p`, the candidate resolves the same
operation declaration under its own capture-avoiding map `φ`; the
monomorphization evidence supports reconnecting its return-effect family item
to the selected typed scrutinee item, from which the candidate derives the
family arguments. The arm payload is typed at `Aφ`; the raw continuation
accepts `Bφ` and returns the scrutinee result with the scrutinee's suffix
bound, as in the shallow catch judgment above. This does not identify the
request's separate instantiation `θ` with `φ`, and does not establish callback
visibility or effect routing.

Every proposed relation derives `Demand(v,o)` from its source-rule premises
for the result views whose validity uses it. For callback comparison those
views include the actual/formal row relation and typed application result;
for handler reconnection they include the selected scrutinee item, arm, and
continuation. The demand precedes ledger insertion. Each transition must add
a pending formula or proof-carrying record and establish its directed paths
to demanded outputs. The arm's own requests remain separate origins and are
not offered to this activation. A same-head conflict cannot be hidden by
retaining only the erased family head.

In the minimized witness, the actual callback has latent row `[ask bool]`,
while the handler function's formal callback row is `[ask int]`. Under the
candidate callback-row comparison, these are the two endpoints of one
same-head row relation, so it emits `bool <: int` and `int <: bool`. Since the
candidate's distinct primitive bases have no common solution, the source
application is rejected before runtime. A request-local comparison alone
would not reject this case: it could compare `ask<bool>` to its actual row and
the handler arm to its formal `ask<int>` independently, with both
constraints reflexive. The cross-boundary actual/formal row relation is the
necessary source premise. This deliberately drops the frozen Oracle's
observed acceptance of that ill-typed program if the candidate rule is
approved; it does not make `ask<int>` and `ask<bool>` distinct operation
identities. The compatibility exception was already recorded from concrete
VM and interpreter results. The candidate locates the constraint at function
argument row comparison, but this source rule remains unapproved and must be
proved sound and principal.

An open row whose family shape is not yet known generates no invented row
head and no premature pairwise constraint. It retains the typed request and
its family arguments; when a later row operation establishes a same-head
match, that transition emits the key before moving/removing the head. If no
such match is established, the request remains in the open/support evidence.
This preserves unknown shape without postponing a known obligation until
materialization. The candidate source derivation still depends on a selected
language rule for effect-row annotations and handlers, and the route/owner of
`Eθ` remains unresolved; those gaps prevent treating this rule as authoritative.

#### Callback-row polarity is not determined by the typed-family witness

The `[ask bool]` / `[ask int]` witness establishes that a sound source system
must not let a callback produce an operation result inconsistent with the
handler arm's continuation input. It does not establish the direction or full
shape of callback effect subtyping. In its ordinary argument-effect branch,
the frozen Oracle characterizes function argument effects as contravariant,
but its weight routing is not semantic authority under the user's instruction.
The successor must derive the callback rule from its declarative
computation/effect semantics and function variance rule.

The same-head family invariant is direction-independent once two typed rows
are known to meet: either orientation emits both `τ <: υ` and `υ <: τ`.
However, row support and tail constraints are directional. For example,
`{ask} ⊆ {ask,io}` holds while the reverse inclusion does not. Therefore the
closed/open `RowLeq` characterization cannot by itself select whether an
actual callback row is the left or right endpoint of the function-argument
comparison, nor can same-head invariance justify an orientation for unmatched
effects. The minimized witness has equal support on both sides and cannot
distinguish those choices.

Until the independent function/effect variance rule is derived, retain only
the soundness obligation: any callback path that can produce an offered
same-head request must preserve its symbolic family-argument constraint to
the matching handler/continuation view and check that constraint before final
acceptance. Merely retaining a detached or unchecked formula is insufficient.
Do not claim the candidate actual/formal callback comparison is the selected
source rule or that it is principal for the language. The witness justifies
rejecting that concrete unsound acceptance; it does not identify the Oracle's
internal missing edge or settle compatibility for programs with differing
effect supports.

#### Conditional callback effect-contract rule

This records one independently checkable rule under a narrow semantic premise:
an effect row attached to a callback parameter denotes an upper bound on the
typed requests that any supplied callback may emit when called. It does not
derive when a handler may intercept those requests; visibility and grant
lifetime remain separate.

Let a supplied callback value have a sound finite-prefix summary
`(R_actual,Q_actual)`, where `R_actual` is a typed latent row and
`E_actual = support(R_actual)` is only its erased support projection. Require
the source invariant that every known typed request in `Q_actual` is represented
by its typed family occurrence in `R_actual`. If any possible request remains
unknown, widen `R_actual` with `TopEff`; do not silently omit it or assign it a
family. `TopEff` denotes unknown support, is not covered by a finite row, and
is covered only by a formal top bound. Let the receiving parameter declare
typed latent row `R_formal`. Before the receiving function is callable,
require the symbolic typed-row constraint:

```text
TypedRowLeq_s(R_actual, R_formal)
```

where source site `s` defines the support comparison and the exact selected
within-row/cross-row occurrence pairs whose arguments must be invariant. The
all-pairs `TypedRowLeq` above is only a maximal stress instance; it is not
implied by the symbolic-retention requirement. Keep every source-selected
obligation and its request/row incidence in `K_sym`; solve it before final
acceptance or retain it as a residual scheme constraint. If the callback is
generalized, freshened, or intruded, transport its actual row, the formal
contract, and every selected formula endpoint under their shared binder
ownership. Never rebuild the relation from a materialized row.

Conditional soundness: assume (i) every finite request prefix of the actual
callback is represented in the typed `R_actual`, including `TopEff` for every
unknown possible request, (ii) `TypedRowLeq_s` treats `TopEff` as uncovered by
any finite formal row and includes the source-selected typed family relations
needed for signature coherence, and (iii) every
offered request/selected handler-arm pair has a source-derived signature
coherence proof. For exact operation `p`, resolving the request under `θ` and
the arm under `φ` must prove payload flow `Aθ <: Aφ` and resume flow
`Bφ <: Bθ` (or a representation-compatible equality/coercion theorem),
including binders in payload/result types that are absent from the family's
argument projection. These obligations use the actual request and arm
signature instantiations and remain attached to `K_sym` with their
`InvArgs` evidence. Then row inclusion bounds request support, invariant
arguments preserve the family-indexed part of the operation signature, and
signature coherence makes handler delivery and resumption type-safe. Unknown
identity or unknown typed family does not prove coherence and cannot justify
handler subtraction. A callback with unknown requests is therefore rejected
against a finite formal row or remains unaccepted until its summary is
refined; it cannot use finite support inclusion as evidence of safety. Under
the candidate cross-row selector for the minimized witness, support inclusion
passes because both rows contain `ask`, while its family constraint is
unsatisfiable, so that application is rejected by this unapproved rule. This
example does not discharge the separate operation-only-binder obligations.

The existing assignment-wise open-row lemma proves exactness only for
`Sel_all`. Each source selector `s` needs its own denotation and pair
selection proof before the conditional callback rule can claim
`TypedRowLeq_s` is exact. No principality or weakest-solution result for the
callback source rule is currently established. Even if that relation is
proved exact, the rule that finite rows do not cover `TopEff` remains a
conservative rejection convention, not a proved greatest solution property
for an unknown-row language. This conditional effect rule proves no callback
payload/result safety on its own. It does not establish that the Yulang
annotation syntax has this meaning, the outer function-argument variance, the scope of
handler grants, callback receipt across curried stages, the adequacy of the
family-argument projection, or principality of the combined effect system.
Those premises require source semantics and approval before implementation.

#### Handler operation-signature coherence for independent instantiations (conditional lemma)

The callback contract's family arguments do not necessarily contain every
operation binder used by payload and result types. This lemma makes the
required request/arm bridge explicit without identifying their instantiations.
Let one operation declaration have scheme
`op : ∀b̄. A -> [E] B`, exact path `p`, and family projection
`F<ρ̄>`, where `ρ̄` may mention only part of `b̄`. Resolving a request uses a
fresh map `θ`; resolving the matching arm uses a separate fresh map `φ`.
Neither map is substituted for the other merely because the operation paths
match.

For an exact-path request `q` and arm `h`, emit before consuming the request:

```text
K_family = InvArgs(F<θ(ρ̄)>, F<φ(ρ̄)>)
K_payload = Aθ <: Aφ
K_resume  = Bφ <: Bθ
K_op      = K_family ∪ K_payload ∪ K_resume
```

The subtype judgments on `A` and `B` are structural and include any nested
latent function/effect constraints. If the selected source subtype relation
does not imply runtime-safe value transport, replace those judgments with its
representation-compatible coercion/equality evidence. In particular,
`K_payload` and `K_resume` include every operation-only binder that affects
`A` or `B`, even when it is absent from `ρ̄`. `K_family` still remains a
separate symbolic obligation; it cannot be replaced by payload/result
constraints or reconstructed from concrete rows.

Conditional type-safety argument: a request supplies a payload inhabiting
`Aθ`; `Aθ <: Aφ` makes it safe for the handler arm's payload pattern. The arm's
continuation accepts values of type `Bφ`; `Bφ <: Bθ` makes each value safe for
the request's original continuation, which expects `Bθ`. This uses the
standard shallow-handler boundary: the matching arm receives the raw
continuation and supplies its resumed value to that continuation. The proof
is conditional on the chosen subtype/coercion relation being sound for the
runtime representation and on both sides resolving the same exact operation
declaration. It does not derive handler eligibility or effect routing.

`K_op` names only this operation-value coherence set, not the complete
operation contract: declared latent effect obligations `Eθ`/`Eφ`, including
binders that occur only there, retain their separately source-defined owner
and routing obligations. This lemma does not assign that ownership; those
typed effect obligations must still be transported symbolically by the
general lifecycle rule.

Each obligation has an incidence key containing the exact `OpId`, request
occurrence, arm occurrence, binder ownership, and constraint role
(`family`/`payload`/`resume`). Apply solving substitutions uniformly to all
three value-coherence groups. Generalization, fresh instantiation, residualization, and
intrusion transport the full keyed set with `θ` and `φ` still distinct, as
well as every `InvArgs` endpoint. This directly blocks the case where
`F<>` (or `F<T>` with an unrelated operation-only `U`) matches by family but
the request uses `U=bool` and the arm uses `U=int`: the family formula alone
is vacuous, while payload/result constraints reject the unsafe pairing.

For this fixed operation/arm pair, the displayed payload and resume
obligations are the direct premises of the two runtime value transfers, and
`K_family` is the selected typed-family matching relation. This is a local
coherence lemma, not a proof that these are all and only the source language's
handler constraints, nor a principality theorem for effect routing. The
source elaborator must derive the keys and dependent `Demand` edges before
handler matching removes or forwards any row occurrence.

#### One callback application feeding one shallow catch (conditional composition)

This composes the preceding local lemmas without selecting the open source
semantics. Assume the callback parameter contract has the upper-bound meaning
from the conditional callback rule. Let the actual callback have typed row
`R_a`, finite-prefix request facts `Q_a`, and symbolic obligations `K_a`; let
its formal parameter declare typed row `R_f`. The receiving function invokes
that callback under a shallow catch `H`. The *complete scrutinee expression*
has result `S`, support bound `E_s`, request/evidence view `Q_s`, and symbolic
constraints `K_s`. Its source derivation must include evaluation of the
callee/arguments, callback invocation, and all other work in the scrutinee.
It requires the candidate source-site relation
`TypedRowLeq_s_cb(R_a,R_f)` at callback application and includes that
relation, `K_a`, and all other scrutinee constraints in `K_s`. `Q_s` is not
just a renamed copy of `Q_a`: it contains the callback facts transported
through invocation and source-derived boundary events, plus every other
possible scrutinee request with its own type/route evidence. `E_s` must cover
every finite request prefix of this complete scrutinee and every request fact
in `Q_s`; any unknown request adds `TopEff` to `E_s`. Boundary events may
change visibility/route evidence but may not silently add or remove request
support.

For each offered `q ∈ Q_s` selected by `H`, require exact operation-path
coverage and the independent request/arm coherence obligations from the
preceding lemma. For each offered request not covered or not visible at this
activation, preserve it as forwarded evidence. A family may be removed from
the shallow result only with a route certificate covering every offered
occurrence; raw-continuation-only routes remain charged through `E_s` and the
arm's latent continuation type. Unknown support contributes `TopEff` and
cannot be dropped. The resulting candidate judgment carries:

```text
K_out = K_s ∪ K_value ∪ K_operation ∪ K_route(H,Q_s)
Q_out = Forwarded_H(Q_s, Drop_H) ∪ Q_value ∪ Q_operation
E_out = (E_s \ Drop_H) ∪ A_value ∪ A_operation
```

`K_s` includes the callback/application relation and all scrutinee constraints;
`K_value` and `K_operation` include the respective arm-body constraints and
the `K_op(q,h)` coherence set for every handled `(q,h)` pair. `K_route`
contains symbolic visibility/coverage certificates, not a Boolean
reconstructed from support. Every part of `K_out` keeps incidence to the
requests, arm, continuation, and result views whose validity depends on it.
Solve or transport the constraints together through all named lifecycle
phases; any discharged formula needed by a later route remains as proof
evidence.

Conditional finite-prefix theorem: if the callback upper-bound premise covers
all its finite request prefixes, the complete scrutinee derivation proves that
`E_s` covers every finite request prefix and every request fact in `Q_s`,
`TypedRowLeq_s_cb` is sound for that meaning and selects all typed-family
comparisons required by its callback source rule, every handled request has
sound signature coherence, `Visible` and route
certificates are sound for the current activation, raw `k` retains `E_s/Q_s`,
and arm judgments bound their own requests, then each finite request prefix
after application and catch is contained in `E_out`, and every consumed
payload/resumption is type-safe. This is the composition of callback-prefix
coverage, the two value-transfer inequalities, and the one-step shallow
handler simulation; it does not rely on any weight routing.

Two controls delimit the theorem. With finite supports `R_a={ask}` and
`R_f={ask,io}`, the chosen upper-bound relation passes; the reverse row order
fails support inclusion, although a same-head `InvArgs` remains symmetric.
With family `F<>` and an operation-only payload/result binder, the family
constraint is vacuous, but `K_payload`/`K_resume` still reject a Boolean
request paired with an integer arm. If any premise or required incidence path
is missing, this theorem gives no acceptance; it cannot be repaired by
materializing rows after inference.

This composition remains conditional and non-authoritative. In particular,
source annotation meaning and function variance, callback receipt across
curried stages, `Eop` ownership, construction of `Visible`/`K_route`, and the
source-to-runtime correspondence are still open. The theorem establishes
neither a complete handler rule nor global effect principality. Its premises
are the bounded proof target for the ordinary effect/handler gate.

#### Closed typed-row subtyping fragment (conditional lemma)

The callback comparison above needs a precise local meaning independent of
Oracle weight propagation. Fix a preorder `(Ty, ≤)` for value types whose
satisfaction is equivariant under capture-avoiding type-variable renaming.
Consider only canonical closed rows with one item per family head and a fixed
arity for each family:

```text
r = { F₁<τ̄₁>, ..., Fₙ<τ̄ₙ> }
support(r) = { F₁, ..., Fₙ }
```

For two such rows `r` and `s`, define a typed coverage judgment under a type
assignment `ν`:

```text
r ⊑ᵗ s  iff
  support(r) ⊆ support(s)
  and for every F in support(r) ∩ support(s),
      ν(τᵢ) ≤ ν(υᵢ) and ν(υᵢ) ≤ ν(τᵢ) for every family argument i
```

The symbolic constraint generator returns the structural support check plus:

```text
K(r,s) = ⋃_{F<τ̄> ∈ r, F<ῡ> ∈ s} InvArgs(F<τ̄>, F<ῡ>)
```

The soundness/completeness lemma for this finite fragment is direct: for every
assignment `ν`, `r ⊑ᵗ s` iff support inclusion holds and `ν` satisfies
`K(r,s)`. When support inclusion passes, the generated formula is an exact
characterization, hence weakest up to logical equivalence relative to this
row relation: it asserts the argument relations required at common family
heads. A non-entailed constraint
for absent heads or unrelated binders would strictly restrict the solution
relation without being required by `⊑ᵗ`; an atom entailed by the other
constraints is redundant even if syntactically present. This is not a
principality claim for the full source language. If the row
relation fails structurally, the failure is reported independently of type
constraints. If it passes structurally but `K` is unsatisfiable, no typed row
comparison exists.

For the minimized callback witness, both supports are `{ask}`, so the
structural check passes; `K` contains `bool <: int` and `int <: bool`, which
has no solution when `bool` and `int` are inequivalent in the candidate
primitive preorder (at least one direction of subtyping fails). For `[ask α]`
against `[ask int]`, `K` instead retains the
symbolic pair `α <: int` and `int <: α`; it is not reconstructed from a
materialized row. The request's exact `OpId` remains outside this row relation
and must be carried separately for handler selection.

Type substitutions act homomorphically on formula syntax:
`σ(K(r,s)) = K(σ(r),σ(s))` while both canonical rows and their attached
obligations remain present. Semantic satisfaction is preserved by assignment
pullback: for every formula set `K`, substitution `σ`, and assignment `ν`,
`ν ⊨ σ(K)` iff `(ν ∘ σ) ⊨ K`, assuming type-expression evaluation commutes
with substitution. Under a fresh renaming, compare assignments related by
`ν' ∘ σ = ν` on the renamed variables; keeping the same assignment while
changing an identity is not a preservation claim. No phase may recompute the
formula after row projection/removal from materialized items alone; the
symbolic obligation must travel with the transformed graph. Independent row
maps preserve the relation only when they respect the ownership shared by
these endpoints.

This establishes only a simple closed-row fragment. It does not define open
tails, duplicate-head normalization, multi-path nested family rows, actual
source annotation lowering, latent operation-effect ownership, row weight
transport, handler eligibility, shallow continuation routing, recursive SCC
generalization, or full effect principality. Duplicate and open cases need
separate rules that preserve the same symbolic obligations. The lemma is a
local proof component for the candidate actual/formal row comparison, not an
implementation gate or a complete successor effect semantics.

#### Maximal all-pairs open-row relation (stress candidate, not source rule)

Extend only the row-value language, not the handler dynamics. A closed row
value is a finite family-indexed collection of typed row occurrences. Each
occurrence carries its fixed-arity argument tuple and source/evidence owner; a
family can have multiple occurrences after a row tail is substituted:

```text
R ::= { F₁<τ̄₁>@o₁, ..., Fₙ<τ̄ₙ>@oₙ | ρ }
μ(ρ) = a closed finite typed row
```

The row value retains every occurrence; merging explicit items with `μ(ρ)`
concatenates occurrence collections and never selects one tuple as the
representative for a shared family head. Its support is the set of heads with
at least one occurrence. In this maximal stress candidate only, define
well-formedness by requiring `InvArgs` for all pairs of occurrences at the
same head; those obligations keep their own endpoints and owner identities.
This all-pairs condition is independent of merge order because concatenation
is associative and it does not quotient distinct symbolic endpoints. The
successor's source rules must replace this universal selector with the
specific selected-pair relation at each operation site before the model can
serve as a semantic contract.

For two evaluated rows, the stress relation `R₁ ⊑ᵗ_all R₂` means support
inclusion and invariant argument agreement between every left/right
occurrence pair at each common family head, as in the preceding closed-row
relation generalized to occurrence lists. This universal comparison is a
stress case only. A source-selected relation `R₁ ⊑ᵗ_s R₂` must instead
project the pair collection selected by its source rule `s`; no all-pairs
requirement follows from the symbolic-retention invariant by itself. Row
subtraction may remove occurrences from a support view, but every selected
typed obligation and its owners remain in the incidence ledger for dependent
residual, handler, or root views.

Keep each source-indexed open relation `RowRel_s(R₁,R₂)` symbolic. Under a
particular joint assignment of its row tails and type variables, its typed
occurrence comparison uses the pair selector and support rule derived for
source site `s`. It denotes the assignments satisfying that site-specific
relation; it is not a universal claim that every possible tail assignment is
valid. The all-pairs `RowLeq` instance is one stress candidate, not a default
effect row or an approved approximation. Any principality claim is relative
to the selected source relation and constraint language; it is not a claim
that a particular finite row is the least concrete solution.

When a row-tail substitution exposes same-head occurrences, the solver may
When a row-tail substitution exposes occurrences, the solver may retain the
source-indexed `RowRel_s` unchanged and add only the obligations selected by
that relation's source rule over the newly exposed symbolic endpoints. It may
replace `RowRel_s` with a residual relation only after proving both directions
of solution-set equivalence for all assignments to the remaining tails,
types, and evidence owners. For example, a residual relation must still
prevent an unexposed tail from adding a head excluded by the other row. Every
rewrite keeps the original relation key, selected obligations, and owner
incidence (or carries a proof that maps them equivalently). Thus
normalization is not permitted to drop the only typed relation before all
residuals are accounted for. No stage may infer obligations anew from
concrete materialized rows.

Example:

```text
R₁ = { ask<α> | ρ }
R₂ = { ask<int> }
RowLeq_all(R₁, R₂)
```

This all-pairs stress relation does not decide in advance whether `ρ` is
empty or which other heads a satisfying assignment gives it. It restricts
satisfying assignments:
`ρ` cannot add a head outside `R₂`; if `ρ` contains `ask<β>`, the row value
retains both `ask` occurrences and requires `InvArgs(ask<α>, ask<β>)`; and the
row comparison relates every resulting ask occurrence to `ask<int>`. If the
source/formal relation requires an actual ask request to fit the formal ask
item, its type arguments therefore remain symbolically connected to `int`.
No family detail is generated for an unknown tail shape before an assignment
exposes one.

Substitution is relationally stable for this `RowLeq_all` instance:
substituting type and row terms commutes with its denotation, provided assignments are reindexed by
pullback and row merge preserves the recorded duplicate constraints. A common
external-use map must freshen owned row-tail and type binders together;
outer anchors remain shared and independent uses receive disjoint local row
and type identities. Intrusion transports the row-relation graph vertices
through `M`, type arguments through `P`, row-tail binders through a separate
row-binder map, and handler identities through `Theta`. Every transported
`RowLeq`/`InvArgs` incidence edge must be preserved, or a quotient theorem
must establish equivalent joint solutions and root observations.

This is still only a candidate denotation. A structural proof is required
that this row assignment relation coincides with source effect annotations:
at an inference site, well-typedness asks for a satisfying joint assignment;
generalization must preserve the complete set of assignments and uses. A
separate proof must show the chosen solver normalization is terminating and
solution preserving, and closed/open switching preserves the same relation. It does not yet
specify row-tail subtraction, lacks constraints, repeated pushes and shared
pops, nested boundary frames, handler completeness, residual routing, or
runtime request ownership. In particular, the extensional `RowLeq` definition
does not validate any Oracle weight push/pop rule. Those need independent
operational semantics and preservation proofs.

#### Joint transport of open typed-row constraints (conditional lemma)

The open-row denotation needs one map across type arguments, row tails, and
evidence incidence. Let `Θ_map = (P_t, P_r, M, Theta_h)` consist of:

- a capture-avoiding type-identity map `P_t`;
- a capture-avoiding row-tail binder map `P_r`;
- a bijection `M` on the transported live row/evidence occurrence graph;
- a separate capture-avoiding handler/hygiene identity map `Theta_h`.

For this lemma, assume the maps are injective on their owned domains, their
fresh ranges do not capture fixed outer anchors, and `M` preserves and
reflects occurrence ownership and the independently derived `Demand` edges.
It must also preserve and reflect incidence between each ledger record and
its occurrence/formula endpoints. The maps' domains include every owned
identity that can occur in assigned closed tail values; all non-owned caller
and outer identities are fixed. Proof validity must be equivariant: a
`Proved(proof)` record maps to `Proved(Tr_Θ(proof))` exactly when the original
proof is valid. Family heads and exact `OpId`s are fixed; source provenance
labels stay fixed, while per-use occurrence IDs are mapped by `M`. Every type
occurrence in `RowLeq`, `InvArgs`, row entries, requests, handlers, and proofs
is mapped by the same `P_t`; every row-tail occurrence uses the same `P_r`;
every hygiene identity uses `Theta_h`.

The action extends to values assigned to row tails, not only to the syntax of
the row variable. Define `Tr_Θ^row` on a closed tail value occurrence by
applying `P_t` to its argument terms, `M` to its occurrence/owner identities,
and `Theta_h` to any hygiene identity; it preserves family heads, exact
`OpId`s, and immutable source labels. Source and target row assignments are
related by
`μ'(P_r(ρ)) = Tr_Θ^row(μ(ρ))` for every owned row tail `ρ`; assignments on
fixed caller/outer identities agree. `M` extends to the complete row values
in these assignments and is a bijection over the transported owner domain.

For a batch of independent uses, require the owned ranges of `P_t`, `P_r`,
`M`, and `Theta_h` to be pairwise disjoint across uses and disjoint from fixed
anchors. Shared outer anchors remain identical in every use map. A single-use
renaming theorem alone does not establish this joint-use condition.

Write `Tr_Θ` for this joint action. Relate type assignments by pullback:
`ν_t = ν'_t ∘ P_t`; relate row assignments by the row-value equation above.
The target assignment ranges over the transported target identity/owner
image plus fixed external identities, so each admitted target tail value has
a source inverse under `Tr_Θ^row`. The law is quantified over these related
source/target assignment pairs, not over arbitrary target-only identities.
Under equivariance of type satisfaction, row denotation, and proof validity,
the conditional transport law is:

```text
Sat_{ν'_t, μ'}(Tr_Θ(RowLeq(R₁,R₂)))
  iff Sat_{ν_t, μ}(RowLeq(R₁,R₂))
```

The same equivalence holds for every attached `InvArgs` formula, incidence
edge, and proof payload. Proof: `Tr_Θ` preserves each typed occurrence,
including duplicate occurrences, with a one-to-one correspondence by the
extended `M`. Therefore row concatenation, support projection, and the set of
same-head occurrence pairs commute with transport. `P_t` commutes with
argument evaluation and preserves and reflects each mutual-subtyping
conjunct by type equivariance; `P_r` reindexes tail evaluation through
`Tr_Θ^row`; and `M` carries each ledger/formula incidence and independently
derived `Demand` edge to exactly its transported edge. Proof validity and
`Proved` state are preserved by premise. `Theta_h` changes only the
handler/hygiene identities and does not rewrite type or family identity.
Combining these facts proves both directions for related assignments.

The alpha-renaming lemma applies to generalization/use freshening and to an
injective intrusion transport only while `RowLeq` and its dependent evidence
remain in the graph; for multiple uses it also requires the batch
disjointness condition above. A solver substitution may be non-injective and is a
separate case: if row substitution/evaluation commutes with the denotation,
its homomorphic action on `RowLeq` has the pullback identity under the
composed assignment, but that identity alone is not a bijection on
source solution sets or preservation of root/use observations. The solver
must retain the substituted relation/proof; a non-injective type or row
parent map still needs a quotient proof over joint solutions and root/use
observations. Residualization may remove a row view only if it carries the
derived `InvArgs`/proof incidence and preserves an equivalent residual
`RowLeq` relation. This lemma does not prove that residualization rule, source
annotation lowering, or any handler Drop criterion. It is a conditional
transport result, not implementation authority.

#### Higher-order callback effect loss in frozen Oracle (source counterexample)

The frozen Oracle has a shallow source counterexample to sound effect
forwarding that does not depend on exact continuation-sensitive rows or on
typed family arguments:

```yulang
pub act ask:
  pub get: () -> unit

pub call(f: () -> [ask] ()) = f()
pub invoke(): [] () = call(\() -> ask::get())
pub result = invoke()
```

At frozen commit `a58eefc31e22141574b6f20c6a5748151c6d79f1`,
`yulang --no-prelude --no-cache check` accepts this program. Its raw scheme for
`call` has the parameter type `() -> [ask] ()` but gives `call` an empty
return-effect bound (`Bot`); `invoke`, explicitly annotated with the empty row,
is also inferred pure. The Core IR still contains the nested calls
`invoke -> call -> f -> ask::get`. Running the source reaches the actual
`ask::get` request and reports it as unhandled. A direct control
`pub direct() = ask::get()` is inferred with `() -> [ask] ()`, so the missing
effect is specific to the higher-order forwarding path rather than the
operation declaration.

This is a concrete accepted-source conflict with may-effect soundness: a
program whose declared `invoke` effect is empty executes an `ask` request. The
successor rule is that invoking a callback contributes its latent effect to
the enclosing computation, and this relation remains connected through
generalization and each fresh use. Exact trace multiplicity is irrelevant;
the single possible request must not disappear. If the successor's ordinary
effect semantics enforces this rule, it rejects the empty-row annotation or
gives `invoke` an `ask` effect, while the frozen Oracle accepts the pure
annotation. This is a concrete candidate compatibility difference in final
source acceptance; the soundness priority requires keeping the effect.

The probe localizes the observable gap to the inferred/public scheme path, but
does not yet identify whether the responsible transition is constraint
generation, root generalization, scheme projection, or fresh instantiation.
The paired source characterization narrows the trigger: `pub h(f) = f()`
generalizes as `(() -> ['a] 'b) -> ['a] 'b`, but adding the explicit callback
contract `f: () -> [ask] ()` changes the inferred `call` result effect to
empty. The annotated parameter takes a different lowering branch from the
unannotated generic control: frozen `lambda.rs` marks a parameter with an
explicit type expression as `LocalCallReturnEffect::Annotated`, and
`unannotated_local_callee_return_effect` returns its bare `call_effect` before
allocating a `SubtractId` or adding a frame pop. Thus the concrete failing
source does **not** establish an incorrect push/pop route. The generic control
does use the unannotated push/pop path, but it preserves its open effect
variable and is not itself the counterexample.

The observed loss is therefore somewhere in the annotated callback path,
including its function-subtype constraints, explicit contract connections,
solve, or scheme projection. The CLI provides no phase graph to choose among
them. The next proof unit is to trace the annotated parameter's symbolic
effect upper through its application constraint, outer function result, and
generalized scheme, while comparing the generic control; then derive a
preservation obligation without importing Oracle routing semantics. This
counterexample concerns effect support and is independent of the separate
symbolic `InvArgs`/typed-family lifecycle invariant, which remains mandatory.

A source-level pass trace narrows the unresolved handoff. Annotation lowering
connects both polarized function bounds to the parameter; the positive return
effect is a pushed `[ask]` boundary row and the negative return effect is a
filtered stack. At application, the annotated branch uses the bare call-effect
variable and constrains it into the enclosing result effect. Function
subtyping propagates return effects covariantly, and lambda output lowering
places the body effect into the enclosing positive function return effect.
The earlier hypothesis that `lambda_param_public_arg` publishing
`call_public_upper` cuts this route is not supported: its negative effect
projection retains the concrete `[ask]` filter family as a row prefix. The
stronger source finding is that calling the annotated local parameter installs
its annotation pop on the enclosing lambda's latent predicate; lambda output
then wraps the body effect in `NonSubtract` with that filtered pop, despite no
handler in the source. This is the identified source-generated discharge edge
and violates the successor rule that callback invocation contributes its
latent effect to the enclosing computation. The exact solver/compact-projection
mechanism explains the empty result scheme. The same `SubtractId s` is created
for the annotation's `push(s, Set{ask})` on the positive callback return
effect and for its `pop(s)` call predicate, filtered to `Set{ask}`. Function
return-effect subtyping carries the push to the fresh call-effect variable,
and application relates that variable to the enclosing body-effect variable.
The lambda output wrapper contributes the matching filtered pop. During
positive scheme projection, `compact_lower_bounds_from` composes the selected
lower's left weight with the outer output weight; `StackWeight::push_pops`
removes the same-id pushed stack entry when it consumes the pop. The residual
`Set{ask}` filter constrains the open inner effect tail but supplies no `ask`
support of its own. In contrast, the public negative annotation projection
turns its filtered stack into an explicit `[ask]` row prefix, explaining why
the callback argument remains effectful while the enclosing function result
becomes pure.

An isolated call-only witness now has a concrete variable-level trace. It was
run against the frozen checkout with temporary debug-only tracing added to
`constraints/trace.rs` and `compact/collect/mod.rs`; those artifacts are
`/tmp/yulang-effect-forward-call-only-trace.log`,
`/tmp/yulang-effect-forward-call-only-compact.log`, and
`/tmp/yulang-effect-forward-call-only-poly.raw`. The annotated callback type
in `TypeVar(3)` contains the positive `push(SubtractId(0), Set{ask})` on its
return effect. The call result reaches `TypeVar(11)` under the enclosing
`pop(SubtractId(0))` filtered to `Set{ask}`. The projection trace selects
`lower[3]`, `PosId(6) -> Var(TypeVar(5))`, whose left bound has the matching
push. Composing it with the outer weight produces `filter Set{ask}` with no
stack entries, and the resulting compact variable is only `TypeVar(5)` under
that filter. The enclosing compact effect still contains several symbolic
variables under the pop plus this filter-only variable, but no concrete `ask`
row. The subsequent raw scheme serializes `call` with return effect `Bot`,
while its callback argument retains `[ask]`.

This directly traces the source-generated cancellation through the selected
projectable lower and its compact result. The post-compaction step that removes
the remaining weighted/open variables before raw scheme serialization is not
yet proved sound or principal, nor generalized to other lower sets and
contexts. The concrete final acceptance counterexample remains established.
This characterization does not make Oracle's weighted routing successor
authority.

#### Unification correction: row selectors are derivations, not semantic rules

The earlier exploratory notation `RowRel_s`, `R₁ ⊑ᵗ_s R₂`, and its
source-site-selected pair collection should not be read as a preferred
successor architecture. The user's later direction prefers one declarative
typed-row relation. The current candidate is to interpret each assigned row
as a set of typed requests and define comparison by denotational inclusion;
finite `Sel_s`/`Demand`-like witness data would only explain how the solver
proved inclusion. Shared-family invariance is a distinct intersection query
over the same argument denotations, for source-derived occurrences that truly
share one family instantiation. Handler eligibility is derived from the
handler transition and activation context. The all-pairs relation above stays
only as a stress case, and the `s`-indexed relations stay as historical
Oracle/source-characterization notation. See `One denotational row relation
(candidate)` in `notes/design/2026-10-01-coupled-effect-interface-core-draft.md`.

This is not yet a selected semantics. Duplicate-row denotation, concrete
argument interpretation, and source derivation of a shared-instantiation
batch remain to be established before subset/intersection can be connected to
the actual source typing relation.

Follow-up refinement: the preferred candidate now places shared arguments
inside one joint row relation `J_R(ν)`, indexed by source-owned family
instantiation binders. `TypedRow` is a projection of `J_R`, and a nonempty
shared-witness intersection is the nonempty fiber for one such binder. Thus
the intersection is not an independent semantic query/obligation beside row
comparison; it is how this candidate relation enforces a shared binder. The
source must still establish which occurrences share that binder. See the
revised joint definition in the coupled-effect draft. This is still a
candidate, and its duplicate-row/runtime adequacy remains open.

The coupled-effect draft also now records conditional handler equivariance for
injective, capture-avoiding renaming of type/row/request identities and ordered
handler identities. The one-step proof cases are forward, match, and arm/raw
continuation transfer; finite trace observations and may support then commute
with the renaming. This gives a transport lemma without assuming any Oracle
weight routing. It excludes non-injective quotients and depends on proving the
successor's source handler relation is equivariant.

For closed point rows, the coupled draft now expands `J_R` exactly into two
parts: internal argument equality for occurrences sharing each source binder,
and a per-left-request disjunction over same-head right occurrences. The proof
is the set-inclusion definition after point-valued binder fibers are shown
nonempty. This captures where pairwise solver witnesses are useful without
making them semantic selectors. It remains conditional on source binder
ownership and does not generalize to interval/compound arguments or establish
the current Oracle's `InvArgs` expansion as sound.

The quotient caveat now has a concrete model: with `Never < Int < Any`,
independent roots constrained to `[Never,Int]` and `[Int,Any]` have a shared
family-argument witness `Int`, while the complete relation still admits roots
`Never` and `Any`. Merging those roots admits only `Int` and loses a source
solution. Thus interval `FamAgree` is not enough to justify a non-injective
intrusion parent map; quotient preservation must cover root observations too.

The coupled draft now states the exact semantic criterion for any direct
non-injective parent substitution: quotient assignments lift to source
solutions, so no solutions are added; equality of complete observable
solution sets holds iff every source solution has an observationally
equivalent representative that is constant on each parent-map fiber. This
subsumes the point-fragment sufficient condition but is not an implementable
check until the source relation and future-client observation are fixed.

The symbolic transport lemma now covers the full joint typed-row relation,
not only its N-way witness predicate. Under natural argument denotation and
bijections preserving request occurrence and shared-binder ownership, the
transported `J_R`, `TypedRow`, and row inclusion have equal fibers. A solver's
type substitution may itself be non-injective while those source ownership
identities stay distinct; merging the ownership/occurrence or parent identities
is still governed by the quotient theorem.

Solving now has a distinct factorization criterion: homomorphic substitution
preserves formula satisfaction on assignments that factor through `σ`, while
whole-relation preservation additionally requires every source solution to
have an observationally equivalent factorization. This is provided by MGU
theory for first-order equality unification, but needs its own proof for
polarized subtype solving. Symbolic family formulas stay in the substituted
relation; row materialization is not a reconstruction path.

### Correction: do not compare support marginals across assignments

An earlier finite-domain coverage sketch allowed support projections to be
unioned across argument assignments before comparing rows. That loses
correlation and is not a valid row-inclusion semantics. Take two independent
left `F` requests with arguments `a,b ∈ {int,bool}` and the complete assignment
`a=int,b=bool`; the left support is `{F<int>,F<bool>}`. Two right requests that
share one binder `c ∈ {int,bool}` have only `{F<c>}` at every complete
assignment, so neither right assignment covers that left assignment. However,
the union of right supports across assignments is `{F<int>,F<bool>}`, which
would falsely suggest coverage if compared with the union of left supports.

The coupled-effect draft now defines row inclusion pointwise at the same
complete assignment, with the assigned shared binder value retained in the
joint relation `J_R(ν)`. This supersedes the earlier marginal-coverage
formulation in this progress record. It is still only a candidate semantic
relation: the source rule for shared ownership, the argument denotation, and
sound/principal solver support remain unproved.

### Correction: filtering must retain the source fiber

The row-support filter law is a restriction of an already formed relation,
not reconstruction of `J` from the surviving occurrences. If a typed-family
predicate was witnessed through an occurrence that the filter removes,
rebuilding `J_{filter φ(R)}` can make its nonempty-fiber condition disappear
and admit assignments that the original relation rejected. The coupled-effect
draft now writes filtering as `Filter_φ(J^K_R)` while carrying the original
symbolic predicate and ownership incidence unchanged in the complete
interface. This is necessary for the user's solve/residualize/generalize/
instantiate/intrude invariant. The support equations hold for that relational
restriction; they do not prove that the present row-only `J_R` notation is a
durable residual representation.

The same correction now has an exact relation-image statement. For
`Rel ⊆ {(ν,V,Q,K,D)}`, define `Filter_φ(Rel)` by replacing only `Q` with
`Q ∩ φ`. Then `dom_{ν,V}(Filter_φ(Rel)) = dom_{ν,V}(Rel)`, since every
relation member maps to one member and no other coordinate changes. This is
the local proof that filtering preserves all satisfying type/root fibers,
including fibers whose output support becomes empty. A finite solver still
needs a presentation that retains `K,D` and does not reconstruct them from
the remaining row entries.

The coupled-effect draft also separates a typed handler's input-domain
predicate `P_H` from its continuation-bearing relational image. The finite
presentation adds `P_H` to the existing `K` before residual support is
computed. If each admitted interface has a nonempty concrete fiber and the
source transition plus symbolic observation are total there, then the output
valuation domain is exactly `dom_ν(R ∩ P_H)`: every output witnesses such an
input, and every admitted input yields an output at the same valuation. This
makes explicit that a handler may constrain assignments through its source
typing relation, while row materialization cannot silently constrain them
afterward. Source derivation of `P_H` and the required totality theorem remain
open.

The fiber-domain criterion also exposes an acceptance-completeness risk for
finite over-approximations. If a support-only concretization invents a typed
request/payload combination that is incompatible with a handler arm, the
universal `P_H` test can reject a source-derivable valuation whose exact
behavior only contains compatible requests. A two-request-family construction
records this as an abstract countermodel, not a Yulang source mismatch. The
successor must preserve enough request/payload correlation for the source
transition, or use a separately proved sound output widening rather than
filtering away the source fiber. This is a completeness proof obligation,
not a new handler rule or justification for Oracle routing.

The finite-interface adequacy condition is now explicit: each source fiber
must have some finite input view that both over-approximates all of its source
computations and remains handler-safe over the whole abstract fiber; its
finite output must cover every source transition result. Final-acceptance
capability requires such a view for every well-typed source fiber.
Principality then asks for the least sound expressible output for that view.
This isolates the exact representation theorem behind the unified candidate;
whether the proposed constrained-interface language satisfies it is open.

#### Freshening lemma: quantify semantic binders, reindex presentation labels

The generalization/fresh-use lemma is now scoped to one complete published
member-root view at its own source boundary, or to a tuple when one use event
exposes roots jointly. It does not assume that every SCC member shares one
generalization boundary, binder set, or constraint epoch. If root preparation
produces versioned views, they remain separate until scheduler simulation
proves they are projections of one relation.

For that view, the lemma separates the owned type/row binders
whose assignments belong to the semantic fiber from request, owner, and
handler labels used to present sharing and boundary structure. One
capture-avoiding binder renaming is extended to an isomorphism of those
presentation labels preserving request heads and argument positions, formula
endpoints/incidence, shared-binder partitions, owner-to-view incidence, and
handler activation links/stack order; typed-family formulas are renamed with
that same action. Formula satisfaction is preserved under the paired map,
so each independent use has an isomorphic typed-family fiber over the same
rigid outer assignment. Internal SCC references still use the live relation.
The map is sort-preserving but shared by identity: one source `TypeVar` seen
in value, recursive, or Function latent-effect positions receives one fresh
identity everywhere. A distinct row-tail namespace, if the successor needs
one, cannot split source identities shared with those views.
This avoids treating arbitrary instrumentation labels as extra semantic
quantifiers. Source generation of the complete relation, solver preservation,
the independent-use source premise, and non-injective intrusion remain open.
See `Generalization and fresh use as abstraction and reindexing` in the
coupled-effect draft.

The freshening argument now also covers finite joint use batches under an
arbitrary shared receiver context `W`: disjoint local renamings preserve the
conjunction of each copied component formula and `W`, even when `W` relates
observations from different uses. This is equivariance of a joint relation,
not a claim that it factors as a product. It aligns the effect-interface
presentation with the reviewed conditional joint-use theorem in
`notes/progress/2026-09-30-intrusion-joint-use-renaming-review.md`; source
event partition and Oracle root/scheduler projection remain open.

#### Shallow trace: a handled family can escape through one raw resume

The shallow handler clauses admit a minimal semantic counterexample to
subtracting a family after its first matching request. A request `q` whose
continuation immediately issues another request with the same row key is
handled by an arm that resumes the raw continuation once. The first request
is consumed at this activation; the second runs outside it and remains in
the output trace. Thus the family is present in both input and output
support, although row difference would remove it. Two sequential occurrences
and one resume suffice. This is a trace-level proof against family-wide
subtraction, independent of Oracle weight routing; `Drop` requires absence
from the complete handler image.

Frozen-runtime control-flow characterization at `a58eefc3` supports these two
shallow clauses: `eval_catch` dispatches returned values and requests
separately; `handle_catch_request_arm` walks source-ordered arms, passes the
stored raw `request.resume` to a matching arm's continuation, and on final
fallthrough rebuilds the request with a continuation that resumes then calls
`handle_catch_result` again. Pattern failure and false guards continue to the
next arm. This matches the candidate's raw-resume and forward/re-entry shape.
The path/guard-ID and `handler_boundary` checks still select whether an arm is
skipped; they characterize the frozen runtime only and do not define the
successor's `Visible` relation. Source-level visibility and typed transition
adequacy remain open. Evidence: `crates/mono-runtime/src/runtime/eval.rs`
at `eval_catch` and `handle_catch_request_arm` in frozen `a58eefc3`.

The finite source-ordered arm-search equation also has a direct trace
preservation proof by induction on the remaining arm count. Each pattern or
guard request stays in the composed relation, and its resumed state feeds the
next arm/body. Therefore the image support covers every selected-prefix and
suffix request, without claiming that it equals an independent union of arm
rows. For a handler, the terminal no-arm outcome is mapped by `Step_H` to
forwarding the original request with re-entry. This is conditional on the
candidate state-threaded `BindPat`/`Guard` relations being source-adequate; it
does not yet prove their source typing premises or finite solver projection.

The frozen runtime has the pattern-default continuation shape assumed by
`BindPat`: `bind_record_pat` evaluates a field default only when that field is
absent, then passes the result through `continue_value_as_bind`. If the default
returns a request, that helper wraps its continuation so resumption re-enters
the same binding continuation; subsequent pattern fields run only after the
default value is obtained. This corroborates preservation of pattern-prefix
effects, but only characterizes `a58eefc3` runtime behavior. It does not define
the successor's `BindPat` typing rule or dynamic handler visibility.
Evidence: `crates/mono-runtime/src/runtime/bind.rs` and `runtime/thunk.rs` at
the `bind_record_pat` and `continue_value_as_bind` implementations.

The handler-image formulation was tightened to prevent an auxiliary totality
test from becoming a source constraint. The semantic transfer is the image of
the ordinary typed handler transition over the complete input relation;
`Total_H` is only a sufficient condition for preserving the valuation domain.
Failure of universal totality on a finite over-approximation does not itself
show loss of final acceptance. The direct adequacy test is inclusion of every
source transition output in the finite image, with symbolic typed-family
constraints carried by that same relation. Do not conjoin a totality formula
to the scheme or filter its source fiber. This is a draft correction, not an
approved handler calculus; source typing preservation and finite image
principality remain open.

This correction supersedes the earlier wording in `A single abstraction pair`
that required the handler transformer to be defined on every member of the
abstract fiber as a condition for final-acceptance adequacy. That requirement
is appropriate only when proving an everywhere-defined abstract transformer
or preserving an exact valuation domain. It is stronger than the acceptance
criterion for a finite over-approximation. For acceptance, compare the actual
source transition outputs with the denotation of the relational image; extra
abstract behaviors without a typed transition do not by themselves reject a
source fiber. They matter only if their loss causes an actual source output
not to be covered or the output relation not to be finitely representable.
The conditional handler-transfer proof is now split accordingly: output
soundness needs source-computation coverage and a transition/observation
simulation; universal totality is used only by the separate exact-domain
lemma, not by the soundness proof.

The source-computation candidate now spells out one record-pattern field
default as a presence split inside `BindPat`: a present field binds directly;
a missing field composes `Run(default)` with the remaining pattern relation
using the ordinary state-threaded bind. A default request therefore keeps the
rest of the pattern in its continuation, and its symbolic typed-family formula
stays attached to the composed relation. This is a source-runtime
characterization of frozen `continue_value_as_bind`, not a source typing rule;
field-presence constraints and finite principal projection remain open.

The injective bind-transport lemma now has a conditional structural
`BindPat` argument: atomic tests and embedded-expression evaluation must be
equivariant, while composite rules must be relational choices, compositions,
and projections over child bindings. Under those premises, structural
induction gives the record-default case. Its missing-field branch uses the
ordinary resumable-bind equation, so requests and their `K_sym` incidence
travel into the resumed remainder. `RuleExpression` still needs its own
evaluation/naturality premise. This covers injective freshening and parent
renaming conditionally; source typing and non-injective parent quotient
preservation remain open.

This also supersedes the earlier finite-interface adequacy paragraph that
required every computation in the over-approximating fiber to have a typed
handler transition. That condition is not required for final acceptance and
must not filter or reject the fiber. The current gate is source-input coverage
plus coverage of all actual source transition outputs by the finite relational
image; universal totality remains only a sufficient exact-domain result.

An audit found that the resumable-semantics draft used `Prefix` both as an
observation of evaluation that has not returned yet and as a terminal tree
node. Treating an arbitrary finite prefix of a returning computation as a
terminal node would make bind drop the continuation's later effects. The
candidate now treats the computation as a possibly infinite source execution
relation with internal steps, observable `Request` yields and `Return` exits;
`Prefix(τ,c)` is only an observation of every finite prefix before return.
Bind relays internal steps, preserves prefix observations, and attaches its
continuation only to returns/resumed requests. The injective transport
argument is correspondingly coinductive over executions and checks
finite-prefix observations separately. This fixes a notation ambiguity in the
proof candidate; runtime/source simulation remains open.

## 2026-10-02: isolate the finite-closure theorem

The finite `Slot × Origin` candidate now has an explicit conditional
least-closure lemma in
`notes/design/2026-10-01-coupled-effect-interface-core-draft.md`. It separates
the fixed-point argument from the hard source abstraction obligation: if a
complete-lattice presentation has a monotone collecting transformer and a
sound abstraction pair that preserves typed-family predicates and incidence,
then the least fixed point covers all finite concrete executions and is the
least closed presentation in that abstraction. The proof is induction over
execution length followed by lattice leastness.

Independent compiler-referee review found one major gap in the first lemma:
monotone maps plus `X ⊆ γ(α(X))` proved finite reachability and leastness among
`F`-pre-fixed points, but not leastness among all concretely source-containing
and transition-closed abstract states. The lemma now requires the full
adjunction `α(X) ≤ a iff X ⊆ γ(a)`. Under it, an abstract state contains the
initial configurations and is `Post`-closed exactly when it is
`F`-pre-fixed, so Tarski leastness proves the intended within-abstraction
claim. A focused compiler-referee delta review found no remaining issue in
this lemma; it did not inspect the machine/store abstraction or source steps.

This is not yet a Yulang theorem. The abstract domain may fail complete-lattice
closure or effective monotonicity; the abstraction has not been constructed
for calls, force, resumes, mutable stores, or handler transitions; and support
closure alone does not prove complete typed root/use fibers or typing
principality. The immediate proof obligation is now concrete: define the
abstraction/concretization maps and show each source transition's abstract
image is representable and monotone while retaining symbolic family
constraints. The subsequent exact derivation/lifecycle correspondence remains
necessary before implementation.

### Concrete configuration correction: retain live machine state

Applying that obligation to the existing top-fallback relation exposed a
specific omission: its concrete configuration was written as
`κ = (D,L,Env,ctl)`, while the source `Run` judgment and resumption equations
carry a live machine state `s`. The earlier component checklist mentioned
store updates, but the actual `γ` relation did not relate the concrete store
to an abstract coordinate. Therefore the displayed relation could not prove
simulation for mutation followed by a later call/resume, including the
already-recorded two-resume state-feedback witness.

The concrete configuration for this candidate is now read as
`κ = (D,L,σ,Env,ctl)`, where `σ` is the live source store/state passed through
ordinary steps and saved continuations. The finite presentation now includes
a candidate abstract store coordinate `Σ#`, with static cell/value slots and
unknown cases for locations or state distinctions it cannot track. Its
concretization must include every concrete cell reachable through local,
stored, exported, or imported values; a lost alias or state distinction must
widen the affected state and dependent continuation/effect observations, not
silently restore the store captured when a continuation was created. The
earlier relation omitting `σ` is withdrawn as a full-machine invariant; the
revised `Σ#` relation remains a candidate until read/write, alias, state-test,
and resume simulation are proved. Whether a useful finite
`Σ#` retains enough correlation for principal handler subtraction remains
open; sound top widening is the fallback candidate, not an acceptance or
precision claim. A conditional local heap-coordinate lemma has since been
added: canonical many-to-one cell slots plus `Pts#` coverage justify union
reads and weak writes when every current cell value and the transitive
referents of live roots are covered by complete value/formula facts. Two
focused compiler-referee passes found and closed counterexamples involving
different content/reference witnesses and a newly reachable referent; the
repaired local lemma has no remaining finding. Its premise that evaluated
write operands are roots, and source read/write plus capture/resume simulation,
remain unproved.

The least-closure repair received a focused compiler-referee delta review with
no finding: under `α ⊣ γ`, `F`-pre-fixed points are exactly initial-containing,
`Post`-closed abstract states, so its within-abstraction leastness follows.
A separate compiler-referee audit caught gaps in the first live-state
transfer sketch: store taint was absent from the top-edge premise, and the
successor relation did not explicitly preserve non-heap state. The revised
predicate includes `UnknownCell`, `UnknownStore`, and `UnknownState`; the
transfer table covers reads, writes, identity tests, and branches on unknown
state, and requires the successor `Σ#` to cover concrete state without
resetting it. Focused delta review of these repairs found no remaining issue.

## 2026-10-02: keep handler semantics separate from route certificates

The coupled-interface draft had one inconsistent sentence calling route
evidence a semantic coordinate, while its common carrier and comparison
section correctly treated route ledgers as bookkeeping. The sentence now
states the intended boundary consistently: activation-specific visibility and
the handler transition are semantic; a route certificate is derivation
evidence that the transition respects that visibility. This removes a
bookkeeping construct from the mathematical carrier without erasing the
underlying source-level boundary behavior. It is a consistency correction to
the non-authoritative draft, not a new handler rule or proof of source
adequacy.

## 2026-10-02: compare candidate cores by proof reuse

The coupled-interface draft now compares its three candidate layers explicitly:
typed may-rows with symbolic formulas, constrained complete-interface
relations, and continuation-bearing source computations. None is yet proved
sound and principal for the source language. The working proof strategy keeps
continuation-bearing computation as the adequacy reference, tests the
constrained relation as the inference core, and treats typed rows only as a
possible finite presentation of that core. This formulation reuses restriction,
relational-image, fixed-outer projection, and reindexing laws across row
filtering, callback composition, handlers, and SCC lifecycle transport.

Source distinctions count as semantic only when they change computation,
complete typed interfaces, or satisfying assignments. `Sel_s`, `Demand`,
typed-family obligation records, route certificates, and owner/incidence IDs
remain possible finite derivation evidence, not separate semantic constructs,
unless a source observation demonstrates otherwise. Handler visibility is
still semantic and must follow from active source boundaries. Typed-family
predicates remain in the denotation through solve, residualization,
generalization, freshening, and intrusion. The comparison is a proof-target
preference only: finite principal projection, termination, source adequacy,
and SCC quotient preservation remain open.

## 2026-10-02: callback result and shallow-catch boundary

A focused compiler-referee audit found no contradiction in the common relation,
but confirmed that the callback-then-catch simulation cannot yet be proved:
`CallCfg`, `Beh`, source typing, and the immediate-versus-latent boundary are
not defined by an authoritative source judgment. The frozen VM evidence gives
a concrete reason these details matter. `eval_catch` dispatches a returned
value to value arms and a request to operation arms; it does not force a
first-class thunk. `MakeThunk` suspends computation, `ForceThunk` executes it,
and an effect operation emits its request only when forced. A callback's
latent operation row therefore does not determine whether a surrounding catch
sees a request: source context may transport the thunk, force before catch, or
force after catch.

The corresponding minimal simulation must compose strict callee/argument
evaluation, preserve the callback result's latent interface, and let typed
context determine force versus value transport. The same proof must map source
handler routing to `Step_H`, retaining exact operation identity plus request
guard lineage and active ordered frames. A path-matching request may still be
forwarded when its guard lineage hides it from that activation. At fixed type
assignment `ν`, the proof must carry live state, raw versus re-entry-wrapped
continuations, and symbolic family predicate/incidence `K,D`. These are
source-visible computation distinctions represented in the common relation;
they do not justify callback-specific selectors or route semantics.

The new draft subsection records this evidence and proof boundary. It is
operational characterization, not a successor typing rule or soundness proof.
The source-level demand judgment, guard-lineage correspondence, finite
principal presentation, and the resulting final-acceptance comparison remain
open. No tests or implementation were run.

## 2026-10-02: handler image does not distribute through bind

Derived a generic shallow-handler witness against moving a handler image
through continuation composition. A `p` request is unmatched and forwarded;
its continuation returns `v`; then a sequencing continuation emits `q`. The
`q` request is visible after `p` re-entry, a catch value arm preserves `v`, a
`q` arm consumes without resuming, and an outer context resumes `p`. Applying
the handler to the complete `R >>= F` computation consumes the resumed `q`.
Applying it to `R` first, then appending `F`, exposes `q` outside the handler.
So outward support differs.

An independent compiler-referee review confirmed the calculation against the
shallow-handler equations and frozen runtime contract; it required and the
draft now states the visibility, value-arm, and outer-resumption premises.
The result is a general composition law boundary: sequence the complete source
computation before taking one handler image, rather than assuming handler image
commutes with callback/bind effects or row joins. The witness is abstract and
does not establish source typing reachability, `K,D` finite transport, or
principal presentation. No tests were run.

## 2026-10-02: composition associativity under shared identities

Added a reusable law for the unified carrier. Static composition is
associative when independent owners are alpha-renamed apart and
source-shared identities remain one coordinate of the joint assignment:
both associations quantify the same intermediate interfaces and satisfy the
same component formulas. The formula conjunction and dependency incidence
remain present through regrouping, even if an intermediate support projection
no longer mentions a request.

The execution counterpart is state-threading bind associativity up to
observation bisimulation: returns apply both continuations in order, requests
receive the recursively associated continuation, and internal steps plus
finite prefixes of nonreturning behavior are matched. This relies on live
resumed state and appended continuations. A focused independent
compiler-referee review found no issue in these conditional algebraic claims.
The same review confirmed that the law does not authorize moving handler image
through bind; the separate shallow-handler counterexample rules that out.
Source derivation of owner sharing, finite presentation closure, and global
principality remain open. No tests or code were run.

## 2026-10-02: injective transport across static composition

Added the static counterpart to the already recorded handler and execution
bind equivariance lemmas: one capture-avoiding injective reindexing commutes
with `Comp(R,S)` by transporting the joint assignment and intermediate
interface witness. This keeps shared owner identities shared, independent
owners apart, and `K_R ∧ K_S` with its incidence. An independent focused review
found the set-theoretic join argument valid and caught a missing premise for
formula satisfaction; the draft now makes equivariance of every typed-family
atom and injectivity on the complete intermediate interface explicit. This
closes the local alpha-transport claim only. It does not prove source rule
adequacy, solver implementation of the formula, or non-injective intrusion
fiber preservation. No tests were run.

## 2026-10-02: disjoint typed value/computation boundary cases

Added a candidate `Adapt` relation to the coupled-interface draft so immediate
forcing, latent thunk preservation, and thunk-to-thunk adaptation are cases of
one typed boundary relation rather than source-site `Demand` rules. A focused
architect review found the initial clauses overlapped and did not make the
single-assignment scope of the target latent contract explicit. The draft now
gives identity equivalence priority, partitions the remaining cases by source
and target outer shape, and requires the complete delayed computation and its
symbolic typed-family ownership to be covered under one assignment. This
repairs the local ambiguity only. The source typing/elaboration derivation must
still establish which boundary applies, and source execution, handler
visibility, complete fiber transport, and finite principality remain open.
No compiler code or tests were run; `git diff --check` passed.

The same refinement now puts the three thunk cases below a single
typed-boundary relational image over complete interfaces. This makes their
common status explicit: they are candidate consequences of source typing and
evaluation for different outer type shapes, not independent row/effect
transformers. The relation must carry typed-family formulas and incidence
through its image under one valuation. No proof yet establishes the source
boundary transitions, their finite presentation, or the global fiber laws.

The draft now composes that same boundary relation around ordinary function
invocation: target argument to source argument, then call, then source result
to target result. A visibility scope required by the function-boundary
semantics encloses all three parts. Frozen Yulang2 `FunctionAdapter` behavior
characterizes this order, while the successor still must derive the adapter
and visibility scope from source typing and prove that the three computations
compose with one symbolic typed-family assignment. This gives a concrete
source-adequacy target for callback application without a callback-specific
effect rule.

The boundary equation now makes escaping activation lineage explicit. The
frozen guard-marker contract shows that a function adapter's scope is dynamic:
argument/result adaptation participates in the frame, returned values can
carry shape-directed markers, and later force/call re-enters with runtime
identity. The complete interface must transport that lineage alongside `K,D`
and keep runtime-fresh IDs separate from static binders. A plain row or a
compile-time binder rename cannot establish this; the source machine
simulation remains open.

The source-reference capture examples now constrain the common `Visible`
relation directly. A nested-provider pair keeps family and active-handler
shape fixed but changes the result when the receiving callback's concrete
capture row changes to wildcard; the receiver's explicit grant also survives
an intervening wildcard helper. Therefore path-plus-stack visibility and one
unscoped per-family grant are inadequate carriers. The draft compares those
with the complete typed request/interface relation plus source-owner incidence
and activation context, which remains a preferred but unproved formulation.
The immediate source-semantics task is to define ownership/grant scope from
the source annotation relation, including helper, escape, thunk-force, and
scheme lifecycle cases. See
`notes/progress/2026-09-30-intrusion-weight-routing-counterexample-search.md`
for the frozen fixture evidence.

The draft now records a candidate activation-context shape: ordered frames are
paired with source-typed capture relations, and each request occurrence keeps
its source owner and typed-boundary incidence. Visibility asks whether that
same complete relation connects the request to a covering active frame. This
predicts why a helper extends rather than replaces an active receiver grant,
and why continuation re-entry must restore context; it does not yet define
annotation denotations or the escape rule. It is proof notation over the
existing coupled relation, not a new weight or solver construct.

The closure-escape evidence now narrows the lifecycle candidate further: a
capture grant is scoped to active execution, not a permanent family/request
flag. Return unwinds the grant, while a function/thunk value may carry dormant
lineage for later re-entry; the returned closure's latent effect remains in
its type relation regardless of whether a future handler is eligible. This
explains how a sound successor can reject the frozen Oracle's pure returned
closure scheme without conflating effect preservation with handler routing.
The source-level escape condition and exact acceptance effect remain open.
A conditional helper-extension lemma is also recorded: when a helper's source
relation preserves the request occurrence, owner incidence, and prior capture
relation, appending its frame preserves the existing `Visible` witness. The
source typing proof must establish that premise for each helper/adapter path.
The coupled-interface draft also states the local lambda rule behind the
closure fixture: constructing `λ_. f()` is effect-free, but its returned arrow
retains the body's symbolic latent row `E`; a scoped capture relation changes
handler eligibility only when that arrow is called. Generalization and fresh
instantiation use the same binder map for `E` and its `K` formula while
transporting activation lineage separately. This is a conditional ordinary
call/lambda consequence, not a global escape proof or a complete inference
rule.
For typed families, the draft now instantiates the exact lifecycle obligation:
generalize `K_F(α)` jointly with the returned arrow's `F<α>` row entry, then
map both through each independent use's same freshening map. Internal SCC use
keeps the live identity. This applies the already proved injective-renaming
law to the closure preservation lemma; it does not establish the non-injective
parent quotient required by intrusion.
The quotient section now records both the interface counterexample and the
source SCC witness characterized against frozen Oracle above. Unconditional
parent identification is refuted for that source SCC. The abstract
whole-formula quotient lemma is proved conditionally: parent-fiber endpoints
must be equivalent in every satisfying assignment, and formulas/observations
must respect that equivalence. Establishing those premises for useful parent
maps from source typing remains open.

The coupled-interface draft now makes its conceptual economy explicit through
one relational operator basis: join/relational composition, image, restriction,
projection, and identity-map reindexing. Sequencing and callback invocation
are joins and images; splitting/filtering are projection and restriction;
handler residuals are a handler image followed by support projection;
generalization and instantiation abstract or rename owned identities; intrusion
is a parent-map pullback subject to the quotient lemma. These are derivations
over the same complete relation, not new source constructs. The generic laws
include associativity, intersection of restrictions, and composition of
injective renamings. Projection/image commutation, handler distribution over
marginal rows, and non-injective quotient preservation are explicitly not
assumed. This sharpens the preferred theory but does not prove source adequacy,
finite principal presentation, or authorize implementation.

A follow-up formalization made the relational operator signatures explicit.
Transitions are ternary over a fixed assignment and complete input/output
interfaces; sequencing existentially joins the intermediate interface, while
view projection keeps the full type assignment and its constraints. The
associativity proof is the ordinary reassociation of the two intermediate
existentials. This prevents projection from being mistaken for erasing a
symbolic type variable. This is a notation/proof-reuse refinement only; source
transition adequacy, finite-principal closure, and SCC quotient premises
remain open.

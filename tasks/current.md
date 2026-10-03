# Current task: prove and implement SCC-intrusion Function inference

Updated: 2026-10-03. Branch: `research/simple-sub-intrusion`.

Execution state: source work resumed after the user's explicit A decision in
`2026-10-02-source-result-synthesis-choice.md`. The former result-synthesis
blocker is resolved. The full proof-and-implementation objective is unchanged.

## Objective and authority

Prove that the successor plan in `notes/design/2026-09-29-scc-intrusion-generalization-sketch.md` and `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` can preserve soundness and principality while matching Oracle's final well-typed-program capability on the supported envelope, then implement the reviewed and approved inference machine. The full objective remains active.

The redesign charter governs. F5 Function generalization is comparison/rollback material, not the target. User-approved source decisions govern their declared scope; the remaining source theory and implementation require their respective gates. No compiler implementation is authorized yet.

## User-selected invariants

- Soundness and principality outrank Oracle compatibility. A deliberate difference needs a concrete conflict, the dropped Oracle behavior, the successor behavior, and final-acceptance impact.
- Final well-typed-program acceptance matters; inference-stage scheme formatting/acceptance parity does not. Preserve meaningful source constraints; polarity-only `q` erasure is not required.
- Exact traces are a soundness reference. Do not require linear/affine continuation typing merely to infer exact trace support; define principality relative to the chosen sound effect abstraction.
- Keep typed-family constraints symbolic through solve, residualization, generalization, freshening, and intrusion. Prefer one compositional relation over site-specific selectors/obligations. Oracle weight routing is characterization evidence, not authority.
- Callback capture is receiver-activation scoped and preserved through nested transitions. Escaped closures retain latent effects, origins, symbolic `K,D`, and required runtime lineage. Fresh caller handling follows the current source relation; no persistent maker mask without an independent source principle.
- Method selection, roles, and implementation resolution are a mandatory later gate after ordinary effects/handlers settle, unless a dependency appears sooner.
- Shallow handling is primitive; selection, patterns/guards and arms execute outside the candidate. Deep behavior is explicit shallow reapplication to resumed computation; optimizations must preserve that source expansion.
- The user clarified the source reference: every function is a handler/computation receiver. An ordinary value parameter forces and rebinds its input at the start of that same activation; force-before-invocation is a separate optimization obligation.
- Computations are first-class data. Their introduction is inert; after obtaining the callee, application reifies the whole argument with no pre-entry construction prefix. Execution starts only at explicit receiver elimination/handling under the known interface; lookup, transport and latent result shape do not themselves force a computation. Charter §17 closes scheduling choice A as the originally intended source semantics.
- Result synthesis forwards known interfaces: `Result(Value(A))=Comp(empty,A)` and `Result(Computation(E,A))=Comp(E,A)`. Synthesis is inert; an additional pure result layer requires explicit introduction/lifting. Result interpretation is not polymorphic (charter §18).
- Parameter roles are syntax-directed (charter §21): omitted `x` and ordinary `x:A` use value entry, forcing/rebinding once at the same receiver activation even when unused; explicit outer `x:[_] A` / `x:[E] A` retain. Body usage, empty solved rows and latent value shapes do not change roles.

## Milestone state

| Milestone | State | Exit evidence |
|---|---|---|
| 1. Coherent ordinary computation semantics for calls, closures, `Force`, requests, callback visibility, and shallow handlers | Candidate source semantics uses the user's rule: concrete typed callback boundaries govern direct and Force-exposed request visibility; origin/identity/`K,D` remain distinct and `Force` creates no authority | Preserve this boundary rule in Milestone 2; no callback micro-cases without a counterexample |
| 2. Source-to-complete-interface adequacy/simulation | Closed for the candidate ordinary machine: exact embedding covers initial `R`, primitive source-rule images, latent future use, and typed resumptions; bind lifting separately reviewed | This proves the candidate machine embeds in its exact complete interface, not that current Yulang typing derives the candidate binder ownership or has a finite presentation |
| 3. Finite symbolic presentation | Generic finite carrier/certificate theorem, typed transport, symbolic basis, and a conditional two-direction residual factorization lemma reviewed; source-wide guard-context closure and full raw-source realization remain open | Generate every annotation/conversion/invocation/handler comparison with stable provenance; prove finite instance/context closure including replay and sealed transport; construct effective joint residual/projection for unknown Records and feedback; close source refinement and typing/acceptance bridge |
| 4. Generalization, fresh instantiation, SCC intrusion | Waiting on a Milestone-3 presentation | Prove lifecycle transport for that presentation, including external uses, internal SCC sharing, parent ports, and symbolic effects |
| 5. Implementation feasibility | Deferred until milestone 4 determines required surfaces | Targeted architecture/resource audit of the reviewed semantics and representation |
| 6. Implementation | Not authorized | Explicit user-approved design, completed required gates, implementation and verification |

## Milestone-3 finiteness classification

The user directed separate classification of (1) finite but unbounded principal
presentations, (2) infinite unfolding with a finite SCC/regular graph, and (3)
genuinely non-finite presentations proven by a concrete counterexample. Current
evidence now includes a finite heap carrier and principal symbolic interface
for a declared abstract safety-certificate judgment, with fixed finite
program, symbolic basis, and observations. It does not yet establish that
judgment for the complete Yulang source interface. Recursive back-edge graphs and regular stacks are candidate
representations, not yet preservation theorems. A stack-only quotient has a
candidate-machine counterexample from captured-reference aliasing and handler
selection; this does not refute richer finite relational graphs. The full
capture/resumption quotient remains unclassified, and no class-3 impossibility
result exists.

If a later representation is finite per source but unbounded across sources,
an explicitly budgeted structural metric may yield a deterministic inference-
complexity failure, never an `ill-typed` result. Its metric, threshold, check
point, no-truncation behavior, and atomic publication belong to the later
resource design gate; no numerical limit is selected now.

The exact-acceptance quotient inquiry rejects stack-only and independent marginal-store
abstractions that forget captured/caller alias incidence without an exact
selection witness. Investigate a joint rooted capture/store/continuation graph
with shared symbolic `K,D`; this is a candidate, not an established finite or
regular representation. Prove source-image closure preserving actual ordered
selection, latent/resumption future use, existential identities, and shared-`ν`
fibers, then prove least representable projection. Class 1/2/3 remain
unclassified for the complete interface, with no class-3 witness.

A conditional lower bound rules out requiring a total effective quotient
with decidable exact selected-event reachability over an envelope encoding
arbitrary Turing-machine runs: a designated event iff halt would decide the
halting problem. Frozen Yulang features make the encoding plausible, but the
candidate machine lacks recursive/list/enum typing rules, and a resource-
bounded envelope may exclude it. This does not obstruct conservative
principality and is not a class-3 result. Next derive an effective
conservative effect abstraction that retains soundness and principal
projection without requiring exact trace/event reachability. The new
`2026-10-02-finite-abstract-safety-presentation.md` constructs that generic
alternative: finite address/store graphs and a maximal safe assignment domain
with minimal joint observations. Its source refinement, finite symbolic basis,
modular future-use coverage, and acceptance bridge remain open. Possible
spurious rejections are disclosed, not approved.

## Current work

### One endpoint-dependent inequality solver (2026-10-03)

The user clarified that Yulang has one basic query `A <: B`, resolved by
endpoint-dependent solver rules. Do not introduce separate semantic `Bound`
and `Compat` judgments followed by `Resolve`. Variable edges, lower/upper
payload records, replay routes and phase-specific worklists are valid internal
representations of that one inequality. For concrete endpoints, structural
checking, optional Record rules, registered cast lookup and adapter planning
are resolution paths whose evidence/realization attaches to the same query.

The non-composition rule remains: variable-edge propagation may use
transitivity, but success of concrete `A <: B` and `B <: C` cannot establish
`A <: C`. Oracle's optional Record observations provide the discriminator:
`{foo?: string} <: {}` and `{}` `<:` `{foo?: int}` succeed, while the direct
optional-string to optional-int comparison fails. A generated replay is a new
inequality task and needs its own source-preserving derivation; two earlier
resolution successes do not authorize it.

Frozen Oracle stores `A <: X`, `X <: B`, and `X <: Y` in lower/upper/edge
oriented records and may prepare same-pivot replay routes. This supports the
endpoint-dependent solver model but does not prove that all same-pivot pairs
must replay. A failed candidate replay rejects the originating constraints
only if the source bridge proves that replay mandatory. Coverage, incremental
row routes and the alpha/beta fixture remain operational evidence, not source
meaning. The bounded eligible-edge spine is characterized for normalized
constructor payloads; graph-wide source obligation conservation remains open.

The design note
`notes/design/2026-10-03-concrete-compatibility-boundary.md` records the
one-judgment direction and current replay/conversion gates.
`notes/design/2026-10-03-finite-bound-replay-closure.md` is reframed as an
internal solver-state closure theorem; its earlier separate-judgment factoring
is withdrawn. `notes/design/2026-10-03-source-context-finite-closure.md`
records a conditional finite-context theorem for supplied templates, not the
source-wide template-generation proof.

Independent Milestone-3 progress: `open-residual-factorization.md` now records
an exact structural-fiber characterization for one fixed equality-quotient
class bounded by mandatory Records with atomic fields. Its bounded
compiler-referee review is clean. It preserves all `X <= {}` Record
extensions and retains permissions, guards, and `Phi/K,D` on one witness;
it does not solve general residual acceptance or alter the source envelope.

Follow-up bounded result: §7.2 extends the fiber characterization to fixed
closed regular field endpoints. It factors Record-label selection from the
per-label conjunction of the supplied lower and upper field inequalities;
those field fibers remain obligations, not an effective solver. A bounded
compiler-referee and spec-auditor review found no findings. It preserves the
single-witness permission/guard/`Phi` intersection, does not compare endpoint
successes through `X`, and applies only after fixed equality quotienting with
no unresolved flexible class in the endpoints. It does not close source
generation, general residual satisfiability, or any effect/component gate.

§7.3 adds a finite greatest-fixed-point inhabitation test and regular witness
for one closed pure-structural interval of lower/upper endpoint sets, which
decides the unguarded structural nonemptiness of each required field fiber in
§7.2. Compiler-referee and spec-auditor review found no blocking/major issue;
the one minor Record-arity wording ambiguity was repaired and inspected. The
procedure does not decide the same-witness intersection with permissions,
guards, or `Phi/K,D`, and picks no complexity cutoff or source rejection rule.

Immediate gate (reordered by the user's 2026-10-03 clarification): derive the
source-level function-introduction and contextual-elaboration path first:

```text
function literal + expected context
  -> receiver role (pure / handler)
  -> Function interface elaboration
  -> effect-port interpretation
```

Ordinary unannotated function literals infer as pure; an explicit function
annotation selects a handler boundary; callback-position literals receive
handler role from expected context. This pure/handler receiver role is
distinct from charter §21's syntax-directed `Value` versus `Computation`
parameter-entry role. Do not infer the former from Function-port spelling.
The source clauses must establish the interface before assigning meaning to
its effect ports. `never` remains a value bottom, distinct from an empty
effect row and polarized solver sentinels; it has no independent pure/empty
effect meaning.

Immediate bounded subgate: derive source elaboration for the three cases
(ordinary unannotated literal, explicitly Function-annotated literal, and
callback-position literal) before constructing a general contextual challenge
domain. The existing `ref_update_local_buffer_public` call
`r.update (\old -> old + "!")`, together with the public callback signature,
is a concrete expected-context anchor. For each case, record the selected
receiver role, the independently syntax-directed §21 parameter-entry role,
and the resulting Function interface. Then derive the effect-port view from
that interface. Do not give effect-row components uniform receiver semantics;
`never` remains value bottom and gets no effect-position interpretation.

Next derive the pure-function-value to handler-capable callback lift from
source application/elimination. `Force(D) >>= B` explains why a value-entry
handler callback's complete invocation can include both argument computation
`d` and body behavior `b` at reached post-force states. Establish their joint
accounting under the same existing `Rel_C` fiber and `ν`; this does not assume
unconditional row union or four independent general-Type port checks. Treat
`Fun(a, never, b, c) <: Fun(a, d, [b,d], c)` as the target whose port views
must follow from role-specific elaboration, not as an axiom deriving `never`
semantics.

Keep complete `EnvStore`/`JointWF` construction, source alias/store transition
closure, and finite-witness adequacy as later proof gates. They remain needed
for a complete-domain Function comparison but do not block the bounded
source-introduction derivation. Reuse `Rel_C`, `K,D`, occurrence/incidence,
`Flow`/`Observe`, and existing directed-weight/subtraction evidence. The
2026-10-03 reread recorded in the progress audit found old ordered
push/pop histories, family budgets, row split/residual transport and invariant
payload checks already cover the proposed partial reversal vocabulary.
“Reverse addition” is a conceptual reading of that evidence, not a second
carrier. Add no solver carrier or provenance structure absent a concrete
source fact shown unrepresentable by the existing evidence.

Reuse the existing complete `Rel_C` fiber, shared `ν`, `K,D`, occurrence /
incidence, directed-weight and subtraction evidence. “Reverse addition” is
only a possible conceptual restatement of existing witnessed subtraction;
re-read the Astra-era interpretation and directed-stack-weight/effect-
subtraction specifications at the exact bridge where needed. Do not add a
solver carrier, attachment map or provenance structure unless a concrete
source fact needed by this derivation is unrepresentable by those carriers.
After this role-first derivation, identify whether any component-to-carrier
mapping remains genuinely necessary and derive it only for the source-owned
ports and scope.

A diagnostic lift
`⋃{Rel_c | Γ ⊢ c : Comp(E,τ)}` was considered, conditionally transported to
one common challenge/interface carrier, then rejected as effect-component
semantics: it interprets `τ` only as a result-type constraint and supplies no
effect contribution or request incidence. That candidate failure does not
refute every uniform interpretation. Typed-computation-core §9 supplies the
conditional comparison target `D_checked ⊆ D_actual` and
`P_actual(d) ⊆ P_checked(d)` for every checked challenge, but does not build
those descriptions from arbitrary components or Function ports. Use
`Force(D) >>= B` only for its conditional support upper bound over all
reachable post-force outcomes; do not assume unconditional row union.

The earlier source derivation audit found no clause mapping an abstract
effect component to a contribution in the complete receiver/computation view.
The user's role-first clarification changes the research order: first derive
source annotation/context selection and Function interface elaboration, then
reassess whether such a component bridge is still needed. The owning gap is
source annotation/typed-interface elaboration, not a new solver carrier. The
stable-core `[tick 'a; 'e]`
signature is a motivating example only: its expected signature and
`deny_contains` constraints record surface/signature behavior, while
authoritative BracketRow and standalone EffectRowType syntax scopes leave
semantic lowering outside their scope. The admitted fragment versus uniform
scope must follow from the selected source contribution rule, not a
component/type-shape guess. A reviewed candidate for resolved `F(α)` constrains
family support of existing typed
requests and preserves full request data in the complete relation; it does
not establish that this is the source annotation meaning. The abstract
component denotation and component-combination rule remain open. Its
singleton `TypedRow` calculation is conditional on a nonempty argument fiber
in `ArgDen_A`; it composes conditionally with the existing candidate
Function-support clause, but it does not supply the annotation-to-occurrence
rule. A reviewed abstract-view candidate retains the existing `Rel_C`/`K,D`
fiber and states support union only under a nonempty joint fiber and a
source-derived occurrence-union rule; that source rule remains unproved.
Frozen Oracle annotation lowering is recorded as characterization only: its
`items; tail` split and constructor-head subtraction filter do not define the
successor component rule.
Then derive the intended inequalities jointly from the role-specific
complete views, including effectful/diverging value-entry
inputs, ignored retained carriers, dependent
`K,D`, continuation re-emission, and operation callables whose native body
returns a carrier consumed later by the declared result interface. Parameter
roles, call scheduling, result forwarding, and the two target inequalities
remain selected. The role-first introduction/context path is now the immediate
gate; no general four-port Function comparison rule or uniform component
interpretation is selected. Keep
value-bottom `never`, empty effect row, and polarized internal bottom
distinct. Do not use port-wise general-Type checks.

Sol's earlier uniform-first audit confirms the source rules do not derive the
component mapping. Under the newer role-first order, the current evidence
supports only the transport schema
`Interpret(Γ,ν,p,τ)` as a view into existing `Rel_C`, not a denotation. The
earlier binary question about complete-view bounds versus additional
contributions is superseded by the user's role-first clarification. Do not
choose either component interpretation before deriving how introduction and
expected context select the role and elaborate the complete interface. No
new carrier or solver phase is justified by the current evidence.

The bounded source crosswalk now derives the available skeleton: core §6
constructs a lambda from `Value(Fun(P,Result(I_b)))`; §21 generates `P` and
its value/computation entry before body synthesis. Receiver role is an
additional prior choice. For the `ref.update` callback fixture, the ordinary
callback parameter has `Value` entry, so `Force(D) >>= B` gives conditional
joint argument/body invocation accounting. The direct remaining bridge is
how an existing pure-role Function value is checked/adapted at a
handler-capable callback boundary while preserving actual behavior. Derive
that source operation and its complete views before port interpretation;
keep complete-domain/context closure later. No exact `[b,d]` proof or effect
meaning for `never` follows from this slice.

Conditional bridge candidate for the already-constructed pure-role value:
keep its actual introduction role and §21 entry, and let the expected
callback slot supply the handler-capable `CallView` for uses through that
slot. Under identity argument/result transport and `Value` entry, this view
encloses the source order `receipt; Force(D) >>= B`; it does not create a
wrapper force before receipt. The same existing observation path can then
account for argument and body events together. This is conditional until the
source derivation proves that callback expected-context elaboration supplies
that view and its target effect port under the actual/checked domain relation.
The old FunctionMap equation does not prove this placement and cannot be
assumed for non-identity conversions.

The immediate proof target is now the role-directed source elaboration
judgment, not slot-profile projection. State how function introduction and
expected context select pure versus handler receiver role, then how that role
elaborates the Function interface and only then interprets its effect ports.
Derive the three source cases (ordinary unannotated literal, explicitly
Function-annotated literal, callback-position literal), while keeping §21's
`Value`/`Computation` parameter entry independent. Source records currently
give a control skeleton with fixed roles and annotation slots; they do not yet
derive this role-selection judgment or its interface/effect-port clauses.
Do not infer role from port spelling or give effect-position `never` an
independent meaning.

For the unannotated callback literal, the user's callback-position rule
selects Handler and §21 gives `old` ordinary Value entry. The stable-core
`r.update` fixture has a Function-valued callback formal, but core §6 only
synthesizes the argument and constrains its whole computation interface
against the formal; it does not prove the expected interface reaches lambda
introduction before body elaboration. The next lemma must derive that
application/lambda contextualization and preserve inert construction and
receipt/entry order. Treat the prior expected-context path as conditional,
not closed. Function ports and the pure-value inequality remain later.

Bounded target for that lemma: when a resolved callee has a declared
`Value(F_cb)` callback parameter and the argument is a Function literal, pass
that formal's source boundary/profile into lambda elaboration before body
synthesis, then generate the literal's own parameter entries by §21. Record
interface checks as ordinary `A <: B` tasks. Limit this slice to known
Function-valued value formals such as `ref.update`; unknown callees,
computation formals, annotated-literal overlap, effect-port construction and
complete `CallView` inclusion stay later.
The existing static signature template `β∈B` and `Slots(β)` record the
formal/profile; the missing source rule must link the lambda derivation to
`β` before its body is elaborated. At runtime, a callback-boundary source
step instantiates `b=(receiver activation, callback slot, typed contract)`
from `β`. Do not identify this dynamic `b` before a receiver activation
exists. Existing evidence suffices across both levels; no new boundary or
provenance carrier is currently justified.

Current implementation evidence confirms this is a source-elaboration
boundary, not a solver replay gap: `yu-hir::ResolvedExpr` currently carries
only Lambda, Integer, Name and Error, and `lower_simple_chain` resolves only
an atom. Application/CallTail and TypeAnnotationTail remain structural CST/HIR
input; there is no typed application node that can pass a callback formal to a
literal before body elaboration. Keep the next gate on defining the successor
source application/lambda contextualization owner. Do not patch `yu-solver`
to reconstruct that context from endpoint bounds.

Charter §24 now records the clarification as superseding §16's universal
"every function is a handler" receiver-role statement. §16's invocation and
§21 entry mechanics remain conditional on the role/interface selected by §24;
ordinary value entry still forces and rebinds within the invocation for a
pure-role function. Receiver role stays separate from parameter entry.

The role-selection schema has one overlap to cover: a Function-annotated
literal can also occupy a callback slot. Both choose handler role, but the
source relationship between the annotation boundary and expected slot
boundary is not derived. Account for both original descriptors and establish
how their interface check enters the same `A <: B` solver; do not flatten or
merge profiles. The existing core's `Value(Fun(P, Result(I_b)))` supplies
only the result-constructor skeleton, not the role-indexed effect ports.
Working candidate: introduce the annotated literal under its annotation's
handler boundary, then check the resulting Function value at the callback
slot through the same inequality solver, retaining the actual boundary and
expected slot as distinct views. This follows role-preserving value checking
but remains conditional until the source annotation rule establishes that
ordering and the callback `CallView` projection.
The syntax-v0 `as Type` tail is generic syntax and explicitly has no type
meaning/checking authority; therefore syntax shape alone does not establish
this ordering. Keep the candidate conditional until a Function source
annotation/checking clause supplies it.
The current narrow HIR also leaves these source inputs to later elaboration:
`ResolvedExpr::Lambda` carries parameter/body but no type annotation, while
the chain HIR keeps annotation syntax as a generic value node. Recovering the
annotation occurrence and expected callback slot is a downstream producer
obligation after the source rule is settled; compiler implementation remains
unauthorized.

The callback-slot profile projection is downstream of that gate. Once the
handler callback interface has been derived, show how the expected callback
contract creates its `CallView`, typed receipt and identity `Flow`; then show
that `Force(D)` and body requests have separate `Observe` witnesses whose
typed paths reach the same complete invocation effect port under one
`Rel_C`/`ν` fiber. `Inc_C` still checks current activation/eligibility, and
`K,D` remain attached per event. Do not treat a flat row containing both
families as evidence for those path witnesses. The already-constructed
pure-role Function value comparison and complete actual/checked challenge
inclusion remain later gates.

The immediate bounded theorem is the three source-elaboration clauses and
their use at an actual callback literal: synthesized unannotated literal,
explicitly Function-annotated literal, and callback-context literal. Keep the
already-constructed value case separate; it belongs to the later
pure-value-to-handler-interface adaptation proof. Cross source receiver role
independently with §21's value-entry versus retained-computation entry.
Establish the operational `Force(D) >>= B` account for the concrete
value-entry callback and identify which existing request/incidence and
subtraction witnesses track the argument and body contributions. This does
not yet close the complete inequality.

The later full-comparison theorem still must preserve actual entry and
decorated behavior; construct complete source-admissible challenge domains
independently of observed calls or comparison success; retain source histories,
stores, responses, profiles, callback/future-use and resumption; and avoid
acceptance via an empty joint fiber. Only there derive the full joint `[b,d]`
inequality from actual/checked domains and complete observations under shared
`ν` and `K,D`.

The M3 compiler-referee review found a BLOCKING gap in complete-domain
construction and major gaps in decorated-behavior preservation, parameter
entry separation, and support-only lifting. The bounded spec audit found the
selected direction conformant; the semantic proof gaps remain open. No
carrier insufficiency is shown, and compiler implementation remains
unauthorized. See design §8 and the current progress entry.

The existing coupled-interface `CallCfg` and typed-core `D_i` are schemas,
not complete constructions: context typing, other environments/stores and
execution closure remain open. The prior non-vacuity argument uses value holes;
Yulang calls pass an inert whole-argument carrier. A pure-diverging carrier
with empty support distinguishes that challenge from `Delay(Return Unit)` at
a value-entry receiver, even though both have the same result endpoint.
Receipt must precede force, so divergence does not remove the challenge; a
retained receiver may instead ignore it. Later full-comparison gate:
decorated source-context closure and invocation coverage, including
independent source well-formedness of context environments/stores,
source-typed callable/carrier holes, context composition, and preservation of
roles, §21 entry, profiles, `Flow`/`Observe`, `K,D`, future latent use and
resumption. Keep its extensional semantic domain separate from later finite
presentation/principality. These context findings do not block the immediate
literal-role and callback-invocation derivation.

A conditional rigid-hole schema types the context against `T_checked` while
keeping the tested callable out of `Γ`'s semantic environment; the actual
callable, argument carrier and joint environment/store remain separate
premises. Plugging does not get checked-type preservation. The unresolved
BLOCKING issue is that excluding the explicit hole does not exclude aliases
through a recursive captured store. `EnvStore` / `JointWF` need an independent
guarded or well-founded account of captured values and shared cells, preserving
alias identity without requiring the tested comparison. A major
source-context closure obligation remains for storing/copying, alias calls,
handler exit, mutation and resumption. Conditional non-vacuity holds only
under joint source-state premises: the inert carrier reaches actual receipt
before force, even when its computation diverges. This is not annotation
acceptance or a nonempty-fiber theorem.

A conditional proof route uses proof-only rigid holes in open source
derivations; graph identity is available only where the source construction
supplies it. A compiler-referee audit finds proof-only step indexing plausible
for recursive aliases, but leaves exact context-domain and observation-
adequacy theorems open. Approximants must share the same source configuration
and state; every recursive use of `H:T_checked` must decrease the index after
a concrete source transition. Index exhaustion cannot certify membership.

The source-state bridge is also open. Authoritative `docs/yulang3-architecture.md`
§6.9 distinguishes compile-time `StateSlotId` from runtime cell/activation
identity; §8.3 models `&a = value` as pure continuation restart. Frozen
`RefSet` routes updates through `update_effect` and handlers, not primitive
heap writes. Thus generic shared-cell and write-before-resume examples remain
abstract-machine schemas until realized through source State/reference
operations. Do not erase first-class refs from the Function challenge domain;
their source bridge remains separate.

Next: derive two source paths over the same `Rel_C`: (1) visible local
StateSlot operations using existing `StateSlotId`, read/write occurrence and
`StateEffect` facts; (2) general first-class refs via their captured
`get`/`update_effect` callbacks. Define semantic free-variable imports and
source-state transitions exactly; distinguish query-independent imports from
hole-dependent values; prove guarded substitution/history closure through
effect-mediated updates, handler exit, responses and live-state resumption.
Preserve the intended context domain without restricting to closed-program
heaps or enlarging it to arbitrary graph imports. Prove finite-witness
adequacy for the complete interface (domain, receipt, observations, latent
returns, future calls and resumption), not support alone. Existing graph
identity transports supplied states but supplies neither source generation,
complete finite comparison, nor principality. See design §8 for the candidate
and its limits. No carrier change is justified.

Any hypothetical annotation-coverage rule must be a universal obligation over
the supplied complete comparison, not deletion of uncovered observations.
Its support projection applies only after concrete and abstract component
views are jointly defined under the same admissible `ν`, preserving `K,D` and
nonempty fibers. Keep this distinct from request-coordinate filtering, which
preserves the valuation domain. The conditional support consequence below
quantifies only over checked challenges `D_checked`; coverage over actual-only
challenges would be an additional contract condition. Neither support
inclusion nor full-observation restriction alone defines annotation
acceptance. Family coverage also does not discharge full `OpCompat` or handler
checks. These are proof constraints on the next derivation, not a selected
annotation meaning or a new carrier.

Typed-computation-core §9 yields only a conditional support corollary: at a
fixed shared `ν` and each `d ∈ D_checked(ν)`, inclusion of complete
observations implies inclusion after the same supplied request-support
projection `Q`. A precise hypothesis supplies `Allowed(ν,h,O,q)` independently
and requires it for all `h ∈ D_checked(ν)`, all checked observations `O`, and
all `q ∈ Q(O)`; complete-observation inclusion then gives the same predicate
for actual observations at those checked challenges. This says nothing about
actual-only challenges and is vacuous for empty checked domains/observation
sets; it does not establish nonempty typed-row fibers. Keep the same complete
observation boundary on both sides. The concrete family predicate must range
over already established typed requests, while abstract component views and
`Allowed` must preserve the shared fiber. The source gate must construct `D`,
`P`, and `Allowed` from components before this corollary can help either
Function case; it is only a necessary support condition, not complete
annotation acceptance.

Current-code ownership check: `yu-hir` has no effect-row or Function-type
annotation lowering; its current HIR slice preserves syntax values for operator
association and resolves module names. `yu-types`' indexed Function nodes
contain value argument/result only, while `yu-solver::Term` already offers
four-port Function nodes with effect-kind/polarity validation. Treat this as
an implementation map only: existing solver terms do not fill the missing
source denotation or authorize adding parallel evidence machinery. Keep the
semantic gate ahead of any HIR/type-inference wiring.

For that elaboration, map components to existing complete-interface and
subtraction evidence. `g(o)` owns an argument of a typed request occurrence,
not an arbitrary abstract component; one abstract component may denote a
whole correlated row and one concrete component may contribute multiple
requests. Derive its incidence `D`, predicate `K`, and applicable
directed-weight path/split under the same `ν`. A reverse step that claims a
family/key disappears from outward support must establish output absence
through the full handler image: old `L - J` evidence alone cannot rule out
raw-continuation re-emission. Other reverse steps must follow their own
source accumulation rule. Prove existing carriers entail each allowed step
before proposing any new attachment/provenance field. Then prove canonical-
flat covariant and polarity-specific contravariant normalization preserve
that same solution fiber. The two intended inequalities remain constraints;
their exact source elaboration is open. Do not promote Oracle
`Never`/`Any`/empty-row artifacts.

The Astra-era interpretation and directed-stack-weight/effect-subtraction
specifications have been reread as prior art before proposing more machinery.
“Reverse addition” can describe the already witnessed partial subtraction
steps; it does not justify another region, attachment, or provenance ledger.
The genuinely new proof obligations are source classification and
correlation of abstract/concrete row components, covariant flattening
transport, polarity-specific descriptor elaboration, joint resolution of
`[b,d]` and shared-`e`, and a proof that existing evidence justifies each
source-supported reversal. A bounded referee review found no issue in the
conditional §9 consequences recorded for the two intended Function cases;
these do not choose a `never` meaning or a component denotation.

After that crosswalk, return to the distinct fixed application-lane gate:
justify the joint descriptor witnesses/local-exactness premises in §8.2 for
the separate nonreflexive callee Function check and matching cast-candidate
Function check, rooted in the application contract and admitted candidate
branch respectively. Neither check is reflexive or justified by
concrete-success composition. The §8.2 `W_j` is proof notation for views into
existing carriers, not a proposed solver record or separately allocated
attachment/provenance bundle. The fixed-lane audit confirms that ordinary
execution and complete-interface adequacy do not map Function effect-port
spellings to their challenge/observation domains, and the existing comparison
clause is sufficient rather than exact. First derive the source
annotation/checking bridge and candidate-branch contract; then instantiate
local exactness for the callee root and admitted cast branch separately.
After that, prove the conditional fixed-lane boundary/task conservation in §8.2 of
`notes/design/2026-10-03-finite-bound-replay-closure.md`. Broader replay
admission, guards, row/residual alternatives, multi-consumer ownership,
source-template/context closure, residual satisfiability, generalization,
freshening and SCC lifecycle remain separate gates. No implementation
representation or compiler change is authorized by this record. No
tests/builds ran for this documentary gate.

The bounded subgate is the argument lane of one ordinary application with a
literal-leaf argument, non-Record constructor endpoints, one monomorphic
closed Function signature and callee scheme instantiation with no quantified
variables, one consumer, empty weights, no aliases or cycles, and no row
reduction. A source trace derives the fixed fixture's exact scheme and empty
side tables through annotation connection, SCC compaction, and publication;
the fixture itself does not directly assert that scheme. Frozen source
connects the application origin through a callee-pivot Function comparison to an
argument-derived task and selected replay, then independently reconstructs
the materialized consumer check and endpoint-based cast emission. The
specializer also submits a separate callee Function check. For an ordinary
annotated argument effect, inference materializes `Never`, while pure
application construction uses `EffectRow([])`. TaskSolver's principal
inference materialization also turns the positive bottom return effect into
`EffectRow([])`, while preserving the negative argument effect as `Never`.
Frozen specialization decomposes the callee Function into the non-reflexive
child `EffectRow([]) <: Never`, which the current non-fixed-head fallback
accepts. This is historical characterization only. Per the user's latest
decision, Function effect ports are descriptors, not independent general-Type
subtyping fields: both polarities may contain abstract and concrete type
components. Covariant rows use canonical flat form, with correlations carried
by constraints/evidence. Contravariant rows containing only abstract
components may normalize to their meet `[]`. A row with a concrete component
is instead an attachment-preserving descriptor for partial reverse addition,
justified only when the concrete contribution and its attachment in the
accumulated effect are known. It is not a total subtraction algebra. Effect
variables and concrete effect records
are examples, not an exhaustive classification. Components may be mixed in
one row; no privileged body/tail separator is required. Common-variable
collection is only an auxiliary view of the abstract component structure.
Resolve both ports jointly in the same `A <: B` query using the existing
coupled-interface assignment, family ownership/incidence, and transport,
plus concrete matching and correlated residual comparison. Do not introduce a
second shared-correspondence map or attachment/provenance ledger for
“reverse addition”: first determine whether the existing directed-stack-weight
and effect-subtraction evidence (scoped identity, ordered history, family
budget, split, residual and invariant-payload constraints) can express the
source-supported partial reversal. That frozen specification is prior art,
not successor semantics; its transformations need independent source
justification. The genuinely new questions are abstract/concrete component
classification and correlation, canonical-flat covariant normalization,
polarity-specific descriptor elaboration, and joint Function resolution of
the intended `[b,d]` / shared-`e` cases. No Never/Any/empty-row lattice account
is part of this rule. Still open: whether co-occurrence justifies
consolidation without equating original terms; transport of correlations
through covariant flattening; any specifically identified evidence gap the
old machinery cannot express; descriptor elaboration; `[b,d]` combination;
and preservation of family `K,D`.
The exact scheme and bounded two-lane operational crosswalk are source-traced,
while the inference fixture lacks a direct stored-scheme assertion. Record
shapes need their own lane accounting.
It does not preserve one replay identity across those stages. Prove or refute
the two-direction correspondence directly, using the application boundary and
ordered endpoints rather than identity equality; see §8.1 of
`notes/design/2026-10-03-finite-bound-replay-closure.md`. Covered-row and
multi-consumer conservation remain outside this subgate.

The frozen inference fixture already asserts the `int -> bool`
`OneSidedReplayPair`, its `ApplicationArgument` owner and the `42`/`f` source
sites; this closes one fixed inference-side witness. The positive
specialization path is traced from the source-derived scheme: it submits the
same `int <: bool` pair and wraps the argument with the unique cast. The
fixture does not directly assert the stored scheme, and no executed end-to-end
runtime witness or general two-direction conservation proof is established.
Compiler-referee delta reviews confirmed the literal-leaf scope, callee-pivot
transition, unique-cast endpoint path, and the fixed candidate/body-instance
checks inside local cast resolution. A minor overstatement about enumerating
all registered casts was corrected. These reviews do not certify broader
replay conservation.

## Checking normalization checkpoint

Typed-computation-core §7 now separates source introduction/consumption,
proof-only checking of the same decorated interface, and executable admitted
casts. It proves that erasing only checking labels preserves the executable
consumer/entry skeleton, actual source contracts, typed evidence, symbolic
`K,D` and future/resumed execution. Semantic inclusion remains a premise,
not a new opaque solver instruction. The finite bound covers generated code
and constraint roots, not solved query closure or principal inference.

The old `Adapt(Unit,alpha)` tower and its dual are conditional counterexamples
to the old candidate adapter's producer-only inventory, not established
source obligations. Its `FunctionMap` can execute argument conversion before
receiver receipt and therefore is not automatically justified under the
selected source semantics. Bounded frozen source evidence requires outer
computation passage/execution, Function callbacks and ordinary registered
casts; the arbitrary nested-thunk assertions inspected use manual mono
inputs. This is not an absence proof or permission to remove acceptance.

The next milestone package must derive effective relational checking/query
closure for actual source contracts and normalize required conversions to
source introduction/consumption, checking, or admitted executable casts.
Cross-role Function assignments need complete invocation contracts; payload
variance alone cannot erase different receiver entry behavior. Registered
casts remain required; method/role/impl resolution stays in its mandatory
later gate unless a concrete ordinary-effect dependency requires it sooner.
No class-3 witness, complete finite principal presentation, lifecycle gate
or compiler implementation approval follows from this checkpoint.

## Parametric open-row presentation checkpoint

`2026-10-02-parametric-open-row-presentation.md` extends the previous closed
point-row theorem to open support variables. It constructs membership
circuits for union, intersection, relative difference, head filtering and
guarded alternatives, then generates exact inclusion/equality constraints.
Global alternative derivations remain whole blocks, never independently
chosen per request. Shared family endpoints and global `K` stay fixed.

Eligible local row variables have exact finite Boolean projection; a support
witness proves it works for finite rows as well as arbitrary sets. Variables
with surviving incidence or family-argument/guard dependencies cannot be
hidden by that theorem. Monotone recursive equations from the same
zero-preserving grammar admit at most one bit increase per recursive variable
per request, hence at most `n` simultaneous symbolic rounds. Least recursive
closure and the all-solutions relation of recursive constraints are distinct.

This is a concrete finite row-schema construction, not merely a name for
semantic inclusion. Boolean projection may grow exponentially but remains
finite. It supplies no complete source acceptance, contextual Function
checking or exact shallow-handler transformer. The current grounded `PΩ`
basis does not yet cover arbitrary new client endpoints merely because a
parametric membership schema can be applied to them. The next package must
connect those symbolic requests to the joint invocation/handler interface
with typed paths, current state, original contract slots, and future/resumed
use. Full Milestones 3–6 remain open.

## Correlated symbolic-request checkpoint

`2026-10-02-symbolic-request-register-quotient.md` constructs a finite graph
and predicate inventory for a finite-control kernel retaining boundedly many
request points. Equality partitions and unary-query colors preserve their
correlation. Capped existence-of-distinct-points formulas allow every graph
edge to lift from every concrete representative at the same static
assignment, rather than merely one possibly unreachable representative.
The bound includes all old registers and all simultaneous witness variables.

The existing certificate theorem then supplies kernel-relative principal
certificates and exact designated-fault reachability. New point inputs do
not require enumeration of new ground endpoint names. This is neither a
source runtime type-comparison feature nor a complete source theorem.
Dynamic events/activations remain distinct; all source symbolic `K,D`
dependencies must still be represented. Capacity formulas are nonpointwise,
so their row variables cannot use the prior pointwise hiding theorem.

The next owning gate is the typed modular interaction abstraction: derive
finite retained-point representation for arbitrary caller/continuation
behavior, normalize complete payload/response/interface `OpCompat`, and
establish effective interpretation of the resulting symbolic predicates.
None follows merely from the finite number of source sites. No source
counterexample, class-3 obstruction, acceptance restriction, lifecycle
completion or implementation readiness is claimed.

Frozen source gives a concrete compatibility dependency: parameterless
`std::testing::assertion` has an `assert_eq` operation with independent
`'a`, `'left_eff`, and `'right_eff` signature parameters. The declaration
and recorded generic-use fixture show family equality cannot determine
payload and callback interfaces. Normalize operation-local binder ownership
and substitutions before reducing complete compatibility queries. This
does not open method/role resolution; the witness's role constraints remain
outside the current proof gate.

## Operation-instance checkpoint

`2026-10-02-operation-instance-binding-package.md` refines complete
`OpCompat` without a new source choice. Each typed operation instantiation
has one declaration map, retained across payload, response, callback
interfaces, raw suffix and symbolic `K,D`. Family equality forgets local
coordinates. Opening an arm or resuming does not reinstantiate them;
captured endpoints remain shared across all selected events. Actual arm
demands are checked for every reachable selection. Charter §19 corrects the
earlier source-acceptance claim: an operation-local generic binder cannot be
narrowed from caller instances; rigid generic-arm checking must precede
request-specific instantiation. Selected compatibility alone is insufficient.

The reviewed result is local preservation under explicit body/store/typing
premises and finite signature transport with preserved sharing. A shallow
nested-resumption attack shows why this is not a theorem of unrestricted
effectful-let generalization. No frozen acceptance of that attack was
established, and no value restriction or other acceptance change is adopted.
The lifecycle proof must preserve or safely discharge dependent witnesses.

The follow-up architecture audit can generate finite body-demand locations
structurally, but those demands still include complete invocation checking.
For a callback call, ordinary domain/result variance and row inclusion have
not been proved to preserve its actual receiver/capture contract, current
store, ordered selection and future use. The next source package must
construct this common invocation simulation and its finite symbolic closure;
an opaque `CIncl` predicate or an operation/arm Cartesian inventory does not
discharge it. Keep this as one interaction/typing package rather than
proliferating callback fixtures. Live dependencies remain exposed to the
later generalization proof.
No class-3 obstruction, milestone-4 closure or implementation approval
follows from the local theorem. M3 semantic and conformance review found
no major issue; the minor graph-work accounting clarification is closed.

## Counting-aware row projection checkpoint

`2026-10-02-counting-aware-row-projection.md` constructs exact elimination
for joined membership/counting constraints, including the request-register
quotient's restricted `AtLeast` predicates. With maximum threshold `b` and
`h` hidden rows, retained capacity queries through `b 2^h` suffice. Distinct
named aliases are treated consistently; full color partitions construct one
simultaneous witness under the same type assignment. Finite-row and arbitrary
subset interpretations have separate exact feasibility rules; no source
row-domain choice is inferred.

This closes nonpointwise hiding for unary predicates built from row
membership, named equality, family heads and independent global guards.
It does not hide live external `K,D`, solve arbitrary type predicates, or
establish a finite complete invocation interface. The principal result is
an exact projected constraint relation, not source inference principality.
Full Milestones 3–6 and the later method/role gate remain open.
M3 semantic and conformance reviews found no major issue. The minor
decidability clarification is closed: eliminating every row can leave
domain-capacity conditions, so both row interpretations need those facts
to decide satisfiability. Tests/builds/measurements were not run for this
documentary construction.

## Fixed-domain certificate comparison checkpoint

Typed-computation-core §8 constructs the first comparison subcase without
an opaque inclusion leaf: fixed admissible interactions, unchanged actual
entry/contracts/complete evidence, and weaker guarantee support bounds.
Finite paired descriptors propagate assumption/guarantee bits; assumptions,
shared writable dependencies and routing remain invariant. Global row
constraints express only the permitted guarantee implications. Original
symbolic `K,D` and complete request instances stay in place.

The input-callback counterexample rules out treating this as uniformly
covariant Function subtyping: admitting an effectful callback while keeping
the receiver's formerly pure result can fail. No source acceptance rule is
changed. The reviewed raw-resumption counterexample also prohibits using
outward effect support to bound every pre-dispatch routing observation.

The §8 theorem assumes challenge/guarantee classification and an original
certificate; it does not generate either from arbitrary source. Its actual
entry and profile-preservation proof covers future use and raw resumption within the
unchanged domain. This closes one finite comparison kernel, not Milestone 3,
general Function inclusion, lifecycle or implementation readiness.

## Source-derived invocation-port checkpoint

Typed-computation-core §9 constructs whole-carrier and complete-call ports
for the resolved ordinary core and derives interaction directions from its
call, force, request and resumption primitives. Function carrier inputs and
operation responses reverse direction; results and payloads preserve it.
Shared read/write exposure retains both obligations. Finite sign propagation
uses graph back edges; it neither unfolds recursion nor drops `K,D` based
on polarity. §8's stronger whole-challenge freeze is preserved.

The incoming computation cannot be erased from the call interface: a value
receiver with pure body can expose argument effects at entry; a retained
receiver with constant body need not expose any. The complete source call
must include its actual entry, body and designated result consumer with
their existing delimiters. Body result synthesis alone is not its closed
effect bound. This is a consequence of the selected source semantics, not
a new argument-effect generalization or annotation rule.

The semantic containment law reverses inclusion of complete admissible
challenges and preserves inclusion of their joint observations, all under
one assignment. The remaining source gate is a finite presentation of this
input-dependent invocation image and higher-order/store interaction relation.
The direction-classification premise is discharged for resolved ordinary
graphs; arbitrary inferred graph shapes, alias worlds, general Function
inclusion, principality, lifecycle and implementation remain open.

## Heap-backed future-interaction checkpoint

`2026-10-02-heap-backed-client-interactions.md` constructs a command driver
for a supplied finite template-closed signature. Complete typed packets,
saved control and client knowledge use linked heap records. Repetition,
retaining arbitrarily many handles and later reuse need no bounded-register
premise or supplied finite client code. Source authority, operation-instance
maps, current handler context and joint `K,D` remain in those packets and
contexts; the pool itself creates no authority or access to private values.

Command-prefix coverage composes with the existing finite weak-store
simulation. This yields a finite conservative carrier for the declared
signature, not an exact alias/visibility quotient. Universal error reflection
and finite command refinement remain necessary for the principal safety
certificate theorem; existentially finding a compatible packet is insufficient.

The next source gate at this checkpoint was **interface encapsulation / template
closure**: derive a finite parametric or regular representation of arbitrary
admissible client operation-local maps, original boundary profiles and their
shared dependencies. A finite set of public family rows does not provide it.
This is an applicability gap, not a class-3 nonexistence witness. No source
acceptance loss, complete Milestone-3 closure, lifecycle theorem or compiler
implementation approval follows from this command-level construction.
M3 semantic and conformance package review found no findings. Only static
document/diff checks apply; no compiler tests, builds or measurements ran.

## Parametric linking and corrected finite-program target

`2026-10-02-parametric-component-linking.md` separates the charter's
per-finite-program target from the stronger optional goal of one fixed
grounded inventory for every future caller. The next source gate now follows
finite parameterized component summaries, linked before constructing the
program-specific descriptor/query inventory. This preserves a reusable
scheme obligation; keeping source code and re-elaborating it at each use is
insufficient.

Finite graph grafting preserves shared external ports, local binder scope,
operation substitutions, profiles and `K,D`, with graph-size construction
for a supplied finite instance graph. The joint projection/linking law is
exact when hidden witnesses are truly local and every shared dependency is
exposed or bound once jointly. Neither law proves source generalization,
finite instance generation, effective query solving or principal summaries.
Abstract runtime addresses must not identify symbolic binder identities.

After the role-first Function introduction and callback-lift subgate, generate
complete finite source constraint templates and prove their instance
completeness/query closure for finite linked instances. Core §9 supplies
complete invocation ports; the template must
include their input-dependent obligations and joint context, not just body
result rows or an opaque compatibility predicate. Milestone 4 subsequently
must prove that actual generalization/freshening/SCC use generates the
permitted instance graphs. The full objective and implementation gate remain
unchanged; uniform grounded client coverage is no longer a mandatory detour.

The user's `ints_only` correction also removes a false source requirement:
there is no need to infer a caller-restricted scheme that legitimizes an arm
narrowing a generic operation's local `'a` to Int. That declaration is an
error. Preserve the generic arm's rigid quantifier scope in source templates;
shared/captured existentials must not become independent witnesses under each
local universal binder. The complete scoped checking/solving theorem remains
open. This correction does not remove request maps or symbolic `K,D`.

## Uniform arm checking and scoped equality checkpoint

Operation-instance package §§7–9 constructs one generic checking template
with captured/shared witnesses outside the rigid operation-local scope and
body-local witnesses inside it. A fixed, substitution-stable body proof can
be instantiated at every admissible actual request map without caller
enumeration; the request's payload, response, raw suffix and symbolic `K,D`
remain correlated. Pointwise re-elaboration at each concrete type is not
such a template.

The constructive solver fragment is scoped unification for finite acyclic
free-constructor equality conjunctions. It propagates allowed-rigid-name
sets through variable bindings and produces a principal uniform syntactic
substitution, or a contradiction in that fragment. It does not implement
subtyping, recursive/equi-recursive equality, row equality, declaration
bounds or the full inference machine. A rigid parameter is not a concrete
type tag disjoint from Int; failing a uniform equality must never produce
that runtime exclusion.

Generic arm validity removes the false need for caller-restricted local
specialization. The outstanding execution template is the complete
invocation/shallow-handler image: entry effects, callback execution,
actual ordered selection and resumed suffix effects. Valid generic arms do
not justify unconditional family subtraction. Full source generation and
scoped solving still precede lifecycle and implementation gates.

A bounded frozen audit found ordinary fresh signature variables but no
explicit generic-arm universal checking step or narrowing-rejection fixture
in the inspected owners. This is an evidence gap, not a demonstrated Oracle
acceptance conflict: no synthetic source ran. Charter §19 remains authority.
Independent M3 semantic/conformance review found no findings in the scoped
template/equality package. A primary wording clarification makes the existing
raw-suffix/store assumptions explicit: operation-map instantiation alone
does not establish the suffix's effect bound. Static diff checks only; no
compiler tests, builds or measurements ran.

## Constructed ordinary query and execution image

Source-realization §7 expands the reviewed typed-boundary/owner relations
into finite-control heap routines for a finite linked resolved ordinary
template. Exact administrative scans use queues and visited lists of
concrete job tuples, with no user code during the query. Only afterward
does weak-store abstraction apply to all instructions and auxiliary records.
This removes the supplied `Visible`/routing-routine premise for that input.

Negative visibility is preserved by instruction simulation, not by negating
a may-path result. A collision of abstract addresses cannot establish exact
identity or that a concrete query job was visited. Concrete scans terminate;
some abstract scans may loop, while finite joint-state saturation still
terminates and covers each concrete finite scan result.

Search keeps original-event applicability from the yielding boundary, then
runs patterns/guards/finish/arms outside the candidate. New events use the
current outer context. Raw suffixes retain only the prescribed owner/view
and forwarding frames. Output observations occur when requests cross their
particular port delimiter, separately from predispatch observation. The
constructed graph feeds the existing joint reachability/safety/image equations;
generic arm validity does not justify whole-family subtraction.

Remaining source gate: resolved template generation, complete scoped
type/subtype predicates and checking, and reusable parametric summary
completeness. Unknown external callable code/responses still require a
linked provider or justified interaction summary. The graph is conservative;
its source-acceptance bridge and all-source-fault coverage remain open.
The full Milestone-3/lifecycle/implementation objective is unchanged.
M3 semantic/conformance package review found no findings within this resolved
input. Static diff checks only; no tests, builds or measurements ran.

## Essential existential request opening

Charter §20 records the user's source typing decision. A declaration/use
instantiates `forall beta_local`; the handler receives one existential
request package and opens it rigidly. Payload, response, raw suffix (when
dependent), profiles and symbolic `K,D` share the retained witness. Known
family coordinates are not hidden. Uniform checking follows from existential
elimination, and application of the checked proof follows by pack/unpack cut.
No surface existential syntax, runtime box or new execution is introduced.

Caller-private instance equations remain in the joint ledger but are not
assumptions available to the generic arm. Thus all actual callers choosing
Int still cannot justify `kappa = Int`. Aliasing, resumption and dependent
return/store transport must retain the same witness correspondence. Complete
scoped inference, lifecycle and implementation gates remain open.
Independent M3 semantic/conformance delta reviews found no findings in this
source rule and its conditional substitution consequences. Static diff and
reference inspection only; no compiler changes, tests, builds or measurements.

The separate omitted-parameter question was subsequently closed by the user
on 2026-10-03 in charter §21: `my ignore x = ()` has value entry and executes
its argument before its body. Explicit outer computation annotations retain.
Frozen initialization and caller-side `ForceThunk` remain characterization;
the user's source rule, not that placement, supplies authority.

## Executable linking before joint recertification

Parametric-component-linking §7 constructs the merged code/descriptor kernel
from finite generated open templates and supplied instance/link maps.
Whole carriers, actual receiver entry, native return/result-consumer phases,
latent handle code and shared store/context/evidence survive linking. Complete
existential request packets retain one witness through aliases and raw resume.

Query lowering and heap abstraction follow linking; the existing joint
`R_link,S_link,U_link` calculation then covers a changed supplied finite
interaction domain. An earlier closed component certificate or outward row
is not reused as a certificate for newly admitted inputs. The proof covers
every actual successor and finite future-use/resumption prefix under the
supplied interaction envelope. Its principal result remains relative to the
existing abstract certificate judgment.

This removes the supplied merged executable-kernel premise for resolved
finite instances. It does not establish general Function subtyping, arbitrary
client coverage, source-template generation or complete predicate solving.
Next in Milestone 3: derive effective complete checking and source summary
generation/instance completeness. The omitted-parameter default is now fixed
by charter §21. Milestone 4 and the implementation gates remain later.
M3 semantic/conformance reviews found no blocking/major issue; the primary
closed one minor translation-layer notation issue and clarified retained
runtime descriptor dispatch. Static diff/reference checks only; no tests,
builds or measurements.

## Guarded positive closure; emitted-predicate normalization next

Core §6 now generates the outer parameter role, body binding and entry
skeleton for omitted/value and explicit outer computation annotations.
Combining this with the existing result table gives coherent source role
skeletons without body-usage inference. Typed-path/annotation checking and
all ordinary endpoint obligations remain. M3 semantic/conformance delta
reviews found no findings; primary clarified the retained typed-path premise.

The emitted-query audit narrows the earlier blanket signed-subtype gate.
Ordinary routing uses identity/activity/path and original-slot admission;
compatibility is checked after selection. Source-realization §8 separates
operational guards from positive compatibility obligations under explicit
initialization/reachability factorization premises. Other faults and generic
arm `Base` obligations remain. Supplied predicates outside this grammar are
not automatically covered.

For the fixed finite pure fragment, Boolean-labelled Horn propagation closes
one joint bound graph. AND combines premise labels; OR joins derivations.
Pointwise evaluation at one assignment commutes with closure, giving finite
termination and fair-order independence. Retaining original clauses preserves
the joint solution relation under the existing pure carrier laws. Growing
labels reschedule dependents; once-only pair memoization is insufficient.
Occurrence/profile/`K,D` identities and rigid binder blocks remain retained.

The follow-up §9 below normalizes explicit concrete capture admission and
closes the named-query row-realization subcase. Complete checking predicates
and semantic endpoint equality remain. Independent satisfiability of marginal graphs
is still insufficient. This package proves neither full SAT completeness nor
source principality; pure Function decomposition does not handle complete
effectful contracts. No class-3 obstruction or source restriction follows.
Lifecycle and implementation remain later gates. Verification uses static
diff/reference inspection; no compiler changes, tests, builds or measurements.
M3 semantic review found no findings. Conformance review found one minor
omission of the referenced variable-rule side conditions; primary restored
distinct-variable/nonvariable cases and the no-new-bound self case. No new
rule or review round was required; no blocking/major finding remains.

## Concrete admission and joint row realization

Source-realization §9 expands an original explicit concrete capture list into
family-head and invariant tuple equalities. Original slots and protection
remain; wildcard/omitted/result-only annotations do not grant capture.
Handler operation coverage is separate. Broader source annotation forms,
including open-tail capture meaning, are not resolved or rejected here.

Guarded checks, row memberships and capacity constraints are joined into
whole constraint blocks under one assignment before any eligible projection.
In the no-counting named-query fragment, all local rows can be realized on
the finite named support. A finite membership-bit matrix, constrained to
agree on coincident request points, eliminates those rows exactly. This
works for finite and arbitrary-subset interpretations, including no named
points, without domain-capacity premises. Semantic type equalities and active
checks remain residual; no independent marginal type solutions are chosen.

Admission guard replacement preserves the query machine and `R/S/U`.
Certificate case expansion/projection is separate and retains all live
dependencies and complete observations. Projection never crosses a later
rigid scope or changes a uniform source arm into per-instance elaborations.
The package does not close full source principality or permit implementation.
M3 independent semantic and conformance reviewers both found no findings in
this package. Static diff/reference checks only; no compiler changes, tests,
builds or measurements. The separate new level proposal was outside review.

Next: effective semantic equality/disequality jointly with actual checking
obligations, and a proved decomposition of complete payload/response/Function
checks. The named-row subcase is no longer an opaque realizability premise;
general annotation generation and unknown client interfaces remain open.

### Existential scope: eager checks on all derived comparisons

Charter §22 records the user's generation/comparison-time level discipline.
An existential introduced at `l` rejects comparisons/unification with types
at level `<= l`; deeper internal generic constraints may propagate. The
user clarified that transitivity eventually produces the direct comparison
with `Int`, which is checked and rejected there. The primary withdrew the
rigid-versus-flexible question: the alias sequence was not a counterexample
to checking every derived comparison. There is no pending choice on that
question, and no exit-time checker or special quantified solver is mandated.

Operation-instance §8 specifies one guarded comparison entry, with dependency
changes invalidating and requeuing affected comparisons and opposite-bound
consequences. Under exhaustive coverage, its conditional invariant ensures
every recorded comparison has current guard evidence at successful quiescence.
Two independent M3 reviewers found no findings. The theorem does not supply
complete path coverage, semantic guard sufficiency or source principality.
Its proof quantifiers and the earlier equality kernel do not prescribe a
separate rigid node or authorize narrowing an operation-local witness.

The bounded frozen audit confirms levels belong to variables, not nullary
constructors such as `Int`. Existing extrusion lowers effective variable
levels and recursively visits both bound sides. An eager escape check must
therefore follow aliases and transitive structural/bound dependencies, not
birth levels alone. This is an implementation invariant to prove, not a
refutation of eager checking or permission to adopt frozen extrusion as
successor authority. No exit-time scan is proposed.

Charter §23 records the user's variable-only level direction. Constructors
carry no head-level metadata; ordinary structural comparison decomposes them.
The earlier fresh-Function-child argument did not account for original
extrusion and is withdrawn as evidence against that algorithm.

Operation-instance §8 gives a candidate variable-level representation for the
finite acyclic free-constructor equality kernel.
`Allowed(X)={kappa | intro(kappa)<cap(X)}` represents a prefix of the live
opening stack, and intersection is minimum cap. A lexical construction now
derives these prefixes under explicit ownership/restriction premises:
preallocate shared roots in their owning context, preserve captured endpoints,
and recursively restrict unsealed outward dependencies before linking them.
Sibling opening blocks retain distinct identities; deferred comparisons retain
their lexical context. A numeric depth detached from that context is insufficient.

The cap procedure reproduces the existing allowed-set algorithm, including
binding traversal, occurs checks and restriction propagation. Its finite
binding/cap/pair measures prove termination; correspondence transfers solution
preservation and principality for uniform syntactic constructor substitutions.
Consistent name transport and increasing level relabelling preserve these
checks. Neither result is a generalization/freshening/intrusion theorem.
Uniform equality failure is not a negative semantic `Eq_nu` guard result.

The pinned original-source reread distinguishes ordered one-sided variable
bound insertion from the frozen Yulang two-sided rule used by the finite
guarded closure. Their equivalence is not assumed. Original extrusion creates
fresh low-level representatives rather than lowering original immutable
levels. The opening extension must also cover bound insertion that skips
extrusion, retaining free-witness dependencies.

Independent M3 semantic and conformance reviews closed the variable-only and
lexical-frontier delta with no blocking/major findings; one source-line locator
was corrected. Verification: static diff/reference checks and `git diff --check`;
no tests, builds or measurements. Signed solution-relation preservation is
now supplied by the separate finite extrusion package below for unscoped
assignments. Sealed packets, nonprefix contexts, generative heads, recursive
equality and lifecycle remain outside this equality theorem. No source
capability is rejected to fit the fragment; full source principality and
compiler implementation remain later gates.

The next audit found a concrete coverage gap in verbatim Simple-sub extrusion:
extrude writes source links and copied bounds directly, outside `constrain`.
The trace `kappa_l <: X_(l+1)`, then `Record{f:X} <: Y_l`, can publish
`kappa_l <: R_l` through `R.lower` while the outer retry succeeds without
visiting that bound; the negative polarity has the dual `R_l <: kappa_l`.
This contradicts the claim that wrapping only `constrain`/retry enforces §22,
not the user's level semantics. The successor must route/stage every extrusion
edge through guarded comparison; scope safety then holds conditionally on
complete replay. Operation-instance §8 and the pinned audit record this gate;
the separate relation package now addresses exact unscoped preservation.
Independent M3 semantic and conformance reviewers found no blocking/major
issues. Two minor semantic precision points (the opening is at boundary level,
and the conditional invariant needs initially certified visible edges) were
repaired without changing the claim.

### Exact extrusion relation and remaining scoped extension

`2026-10-03-staged-extrusion-solution-relation.md` gives one candidate package:
exact source-order discovery in a private heap, with unchanged snapshots and
no replay feedback, conservatively extends the original unscoped constraint
relation. Assigning each parent the original variable's value proves the
reverse projection; signed source links and structural variance prove the
forward enclosing-retry direction. Literal retained relations over original
family/evidence coordinates are preserved jointly. Variable cycles remain
graph edges, with at most two representatives per input variable in one call.
Fixed-term, deduplicated consequence-only replay preserves the relation and
terminates; this is not a termination theorem for an allocating whole solver.

The diagonal extension can depend on a witness unavailable at the destination.
A conditional greatest-type model supplies an independent uniform upper
approximation despite guard rejection, so unscoped preservation cannot alone
prove scoped completeness/principality. The bounded source audit found frozen
`never` syntax and internal Top, but no admitted source obligation establishing
that countermodel as a Yulang acceptance conflict. No guard exception or source
capability restriction is adopted. Next derive the scoped extension criterion
from uniform source checking, admissible boundary approximations and declared
interfaces, rather than treating rejected graphs as semantically unsatisfiable.
Independent M3 semantic/conformance reviewers found no findings in this
package. Static diff/reference checks passed; tests, builds and measurements
were not run. Compiler implementation, effectful checking and lifecycle
remain open.

### Relative uniform-parent construction

The staged-extrusion package now constructs a witness-independent signed
parent tuple for a fixed original strategy over a nonempty joint hidden
domain, assuming a semantic complete lattice. A raw copied-bound operator is
not necessarily monotone: opposite-sign discovery can copy `N <= Q`.
Retained source links already entail those same-variable dynamic cross-links,
so omitting only those redundant terms from the operator gives a monotone
operator while leaving the full graph intact. Uniform extensions are exactly
its pre-fixed tuples. Their least tuple passes an original-root retry whenever
any extending tuple does, for the fixed original strategy and graph.

This is a relative semantic construction, not source/inference principality
or a finite-expression theorem. No finite syntax has been constructed for
the required joins/fixed point; no non-finiteness result follows. An unchanged
hidden anchor can still invalidate exported-root scope, and arbitrary new-port
invariant/evidence relations are outside the downward-closed retry result.
Next relate this criterion to source-generated interfaces, admissible roots
and the generation-time guard. No source exception or compiler approval is
selected. M3 uses one architect, one documentary producer and two independent
semantic/conformance reviewers; both reviews found no findings. Static
diff/reference checks and `git diff --check` passed; tests, builds and
measurements budget/consumption zero. Implementation and the full objective
remain open.

### Source width and finite regular scoped projection

The next source audit found a concrete local checking obligation that eager
exact-reference extrusion cannot handle completely. Under `x:kappa` and
`f:{} -> Unit`, `f {field:x}` is uniformly typable by record width, with no
comparison involving `kappa`. Eagerly extruding that record against an
unresolved captured outer domain instead creates a forbidden witness/parent
edge. Empty-record patterns and expected-field comparison are established
frozen source evidence; the illustrative full handler program is not an
executed or accepted fixture. The exact-reference theorem remains valid;
mandatory use of that algorithm for every scoped target is retired.

`2026-10-03-scoped-structural-projection.md` constructs partial least visible
supertypes and greatest visible subtypes for finite contractive regular
Primitive/Function/mandatory-Record graphs with opaque hidden atoms. A greatest
availability fixed point over signed nodes selects a shared projection;
coinductive factorization proves its bestness. Construction uses at most `2N`
nodes and `2E` edges, including recursive cycles. Record field omission follows
ordinary width, with no forbidden witness comparison or evidence erasure.

This is an exact finite regular result for the stated structural judgment.
It does not classify the whole source effect interface or reject excluded
types. Generic witnesses remain opaque during checking; concrete proof
substitution preserves soundness, not reflection of arbitrary concrete checks.
Next extend source constraint generation and solving to select such projections
for flexible bound graphs while preserving every original invariant/effect
relation. Declared bounds, lattice constructors, effectful Function checking,
typed-family lifecycle and implementation remain open.

M3 used one architect, one bounded source explorer, one documentary producer
and two independent semantic/conformance reviewers. Both reviews found no
findings. Static source/diff/link checks and `git diff --check` passed; tests,
builds and measurements budget/consumption zero. Task/index/progress records
are synchronized for the coherent research checkpoint.

### Symbolic projection and invariant coordinates

The projection package's §6 extends the structural theorem to declared
covariant, contravariant and invariant constructor positions. Invariant
positions retain the original coordinate when a visible equivalent exists;
having both upper/lower approximations is insufficient. Three availability
bits have at most five profiles, but those bits never decide type equality.
The original symbolic family equations, witnesses and joint `K,D/Phi` remain.

For an open regular template whose holes receive shared closed regular
graphs, a finite Boolean equation system computes exact projection control
and a shared graph recipe supplies the resulting roots. Imports and their
derived projections stay correlated; profiles are not free choices. This
constructs the transformation under shape-changing inputs without claiming
to solve unknown bounds. A predicate can be recovered from projected
coordinates only when constant on projection fibers; equality generally is
not, explaining why original invariant coordinates must survive symbolically.

Next close flexible-bound satisfiability and source-generated joint solving,
including aliases/recursive feedback, without treating the five profiles as
a type model. Effectful compatibility, declared bounds and full lifecycle
remain open. M3 used one architect, one documentary producer and two
independent semantic/conformance reviewers; both found no findings. Static
diff/link checks and `git diff --check` passed. Tests, builds and measurements
budget/consumption zero; no compiler changes or implementation approval.
Task/index/progress are synchronized; the full goal remains active.

### Scoped equality and closed structural solving (2026-10-03)

`notes/design/2026-10-03-scoped-constraint-solving.md` packages the next
finite solver slice. A rational equality quotient merges aliases and matching
constructor nodes, propagates arbitrary finite lexical allowed-name sets
through shared/cyclic descriptors, and factors all scope-respecting regular
equality solutions through residual free classes. This is relative to the
regular constructor equality fragment; original `Eq`, family equations and
joint `K,D/Phi` remain attached.

After quotienting, closed structural subtype checks use a greatest relation on
the finite ordered node pairs, with generation-time scope guards before
structural outcomes. The result does not solve open inequalities. In
particular, `X <: {}` has no principal closed substitution in the fixed-label
grammar, but the original edge is already an exact finite residual; this is
not a non-finiteness witness or source-envelope restriction.

The next theorem gate is principal residual factorization for open heads and
Record extensions, composed with scope restrictions and projection summaries;
its reviewed candidate is recorded in `notes/design/2026-10-03-open-residual-factorization.md`.
The bounded code map confirms this cannot be a generalizer-only rewrite:
current HIR lacks calls/effects, and the solver lacks typed families, symbolic
`K,D`, and relational source profiles. This is feasibility evidence, not an
implementation plan or authority. M3 used one architect, one source explorer,
one documentary producer and two independent semantic/conformance reviewers;
both found no findings. Static link/diff checks passed. Tests, builds and
measurements budget/consumption remain zero. No compiler changes; the full
goal remains active.

### Open residual factorization candidate (2026-10-03)

`notes/design/2026-10-03-open-residual-factorization.md` now states a
conditional factorization candidate over the reviewed regular equality
quotient. Known descriptor comparisons normalize into a finite pair graph;
open flexible-head obligations remain residual edges, so `X <: {}` still
covers Record extensions without selecting a fixed shape. Normalization has
separate scope-failure, structural-failure, and successful-residual outcomes.
Original `Eq`, witness identities, invariant endpoints and joint `K,D/Phi`
remain attached to one quotient assignment; projection summaries are derived
from that whole assignment rather than guessed independently.

The M3 semantic/conformance review found one major missing structural-failure
outcome and one minor missing atomic base case. Both were repaired, and a
fresh semantic delta review found no further findings. This closes review of
the candidate draft, not the factorization proof or open-bound acceptance.
Effective satisfiability, finite joint projection over unknown Record labels
and feedback, source realization/uniform scoped typing, later effect/family
and lifecycle work, and implementation remain open. No source policy or
compiler implementation was approved. Static review only; tests, builds and
measurements remain zero. The conditional finite supplied-template context
closure now has clean compiler-referee/spec-auditor delta reviews; it does not
construct carriers from source rules. After the current Function role-first
subgate, continue with the rule-by-rule source bridge for finite
context/instance carriers, followed by effective joint residual/projection
solving for open Records and recursive feedback.

Within that bridge, the representation-preserving annotation-check fragment
on an already supplied finite typed derivation now has a reviewed root/context
corollary in `notes/design/2026-10-03-source-context-finite-closure.md` §4:
check-site and lexical identity stay fixed through proof erasure, while typed
path transport retains tagged evidence and shared `K,D,ν`. The result does
not generate judgments from raw annotations, choose executable conversions,
freshen schemes, or close derived queries. The next source proof must connect
raw annotations and conversion syntax to these supplied derivations without
collapsing checking into executable adaptation.

Full goal remains active.

The candidate now includes a two-direction normalization-equivalence proof:
the forward direction follows finite discovery paths through the greatest
structural relation; the reverse direction adds discovered descriptor pairs
to the residual-valid relation and proves it post-fixed. A separate M3
compiler-referee review found no issue within that conditional regular
fragment. The lexical comparison package partially grounds inherited context
for its unsealed equality slice and requires alias/level/dependency changes to
invalidate and requeue checks. It does not establish context finiteness for
all source-generated subtype comparisons or sealed lifecycle paths. The next
gate is that source-wide context derivation, alongside effective residual
satisfiability and joint projection; the theorem remains conditional and the
full goal stays active.

The source-wide audit is recorded in
`notes/progress/2026-10-03-source-guard-context-audit.md`. It maps ordinary
structural, annotation/conversion, invocation/callback, request, handler and
family comparison origins. Existing records supply only partial premises:
ordinary parameter/result and invocation-port skeletons, operation witness
maps, and an unsealed lexical equality construction. Annotation/conversion
generation, full Function and store interactions, sealed lifecycle, finite
use-site instance closure and multi-parent context provenance remain open.
The source map yields a candidate context `(origin, lexical openings, witness
map, retained typed evidence)` but selects no implementation representation.
It finds no class-3 impossibility proof; full-source finiteness remains
unclassified.

The current §7.4 recursive-bound candidate separates full-fiber graph
variation from existence-witness size: the `Tₙ` family has unbounded explicit
graphs before label erasure, while erasure under the finite input alphabet
collapses this example. Its compiler-referee delta review is clean. The
erasure argument is limited to unguarded pure structural existence and does
not establish arbitrary guard/`Phi` preservation or complete fiber
representation. §7.4.2 gives the input-bounded existence method for a
single-label unary Record input. The earlier §7.4.3 proposal covered two Record
labels; Sol's bounded derivation finds no use of the binary alphabet: the
§7.4.3 path-domain and head-propagation construction generalizes to any finite
input alphabet `Λ`, subject to its existing atom/mandatory-Record input shape.
The generalized proof is recorded in the design draft and passed independent
M3 compiler-referee and spec-auditor review after one minor wording repair in
this task record. Input clauses retaining Function/other constructor heads, exact
full-fiber and joint-predicate solving remain separate obligations. No
compiler authority or implementation follows.

§7.4.1 decides unguarded structural existence for `Λ=∅`: finite-label erasure
makes Records nullary, after which structural subtyping equals rational-tree
bisimulation and a finite equality quotient plus one primitive atom decides
satisfiability with an `N+1`-node witness. §7.4.2 extends existence to the
single-label unary mandatory-Record/atom input fragment. It reduces full
regular assignments to unary chains, classifies each free root by terminal
category and depth, then solves shared inequalities with finite difference
constraints; a reviewed computable witness bound follows. §7.4.3 extends the
existence method to arbitrary finite input Record alphabets using saturated
path domains and regular head propagation through a finite pushdown system;
`{f,g}` is now just one instance. All three procedures check
original directed inequalities directly and leave the full fiber represented
by the original constraints. Independent compiler-referee/spec-auditor
reviews found no blocking or major findings on the earlier fragments and the
finite-alphabet extension. Input clauses with
Function/other known constructors, guards, permissions, `Phi/K,D`, full-fiber
decision and source acceptance remain open.

## Main records

- `notes/design/2026-10-03-scoped-constraint-solving.md` — scoped regular equality quotient and finite closed structural subtype saturation; the following reviewed candidate addresses open residual factorization.

- `notes/design/2026-10-03-open-residual-factorization.md` — reviewed conditional principal residual presentation candidate; open-bound satisfiability and effective joint projection remain open.

- `notes/design/2026-10-03-scoped-structural-projection.md` — finite regular best visible comparators, invariant-coordinate support and substitution-parametric projection with closed imports; full flexible source constraints remain open.

- `notes/design/2026-10-03-staged-extrusion-solution-relation.md` — exact unscoped graph projection, signed retry, finite consequence replay and relative uniform-parent construction; source-scoped extension criterion remains open.

- `notes/design/2026-10-02-parametric-component-linking.md` — finite grafting and exact joint linking; revised per-program proof target, source summary construction still open.

- `notes/design/2026-10-02-heap-backed-client-interactions.md` — heap-backed command-driver coverage for a template-closed signature; arbitrary-client source encapsulation remains open.

- `notes/design/2026-10-02-counting-aware-row-projection.md` — exact counting-aware row elimination with bounded residual thresholds; complete invocation checking remains the source dependency.

- `notes/design/2026-10-02-operation-instance-binding-package.md` — shared operation-local witnesses, local preservation and generalization interference obligation.

- `notes/design/2026-10-02-symbolic-request-register-quotient.md` — finite equality/unary request-point quotient and uniform lifting; modular source applicability remains open.

- `notes/design/2026-10-02-parametric-open-row-presentation.md` — finite open point-row schema, exact eligible projection and positive recursion; full source interaction remains open.

- `notes/design/2026-10-02-source-result-synthesis-choice.md` — authoritative A: source result synthesis preserves known computation interfaces; explicit introduction alone adds a pure layer; result interpretation is not polymorphic.
- `notes/design/2026-10-02-typed-computation-core-elaboration.md` — constructive source translation, result coherence and fixed-domain certificate comparison; changing interaction domains and finite principal inference remain open.
- `notes/design/2026-10-02-source-call-scheduling-choice.md` — authoritative A: first-class computation introduction is inert, whole-argument reification precedes receiver elimination; conditional discriminator and exact acceptance-evidence limits retained.
- `notes/design/2026-10-02-source-computation-role-elaboration.md` — corrected active source map, producer-placement obstruction and common invocation entry expansion; raw-source scheduling/typing and finite solved/parametric presentation remain open.
- `notes/design/2026-10-02-typed-source-owner-realization.md` — reviewed owner-span/control and typed-view context construction; user-selected outside-image equation.
- `notes/design/2026-10-02-typed-boundary-realization-draft.md` — selected common typed-value transport and reviewed conditional transport/lifetime theorem package; reviewed fixed-shape cyclic adapter construction and symbolic equality; full realization open.
- `notes/design/2026-10-02-source-realization-and-symbolic-basis.md` — finite ownership inventory, conditional operational realization, selected-fault reflection, and exact remaining source definitions.
- `notes/design/2026-10-02-finite-abstract-safety-presentation.md` — reviewed generic finite carrier and principal certificate theorem; source application open.
- `notes/progress/2026-10-02-finite-interface-obstruction.md` — classification, lower bound, construction progress, and review record.
- `notes/progress/2026-10-03-open-residual-factorization.md` — candidate theorem, adjudicated review findings, and remaining proof/solver gates.
- `notes/progress/2026-10-03-source-guard-context-audit.md` — source comparison origins, partial context premises, and exact source-wide finiteness gaps.
- `notes/design/2026-10-02-ordinary-computation-semantics-package.md` — current milestone-1 theorem package.
- `notes/design/2026-10-01-coupled-effect-interface-core-draft.md` — relational carrier and prior derivations.
- `notes/progress/2026-10-02-callback-scope-transition.md` — callback/escape evidence and decisions.
- `notes/progress/2026-10-02-successor-implementation-feasibility.md` — alternating feasibility audits.
- `notes/design/INDEX.md` — design status and authority map.

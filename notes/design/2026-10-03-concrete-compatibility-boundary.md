# One inequality judgment with endpoint-dependent resolution

Status: Draft; records user-directed single-inequality, Function effect-descriptor, and mixed-row directions; merge semantics, complete resolver semantics, and implementation authority remain open
Date: 2026-10-03
Scope: one inequality judgment with endpoint-dependent solving and local concrete cast/adaptation resolution
Approved-by: user for the single inequality judgment, endpoint-dependent resolution direction, concrete-success non-composition, polarity-indexed Function effect descriptors, mixed abstract/concrete type components, canonical-flat covariant rows, abstract-only contravariant meet normalization, and concrete-bearing attachment descriptors for witnessed partial reverse-addition; component classification, co-occurrence consolidation, the component-to-existing-carrier bridge, proof that existing evidence licenses a particular reversal, replay eligibility, and implementation remain open
Reviewed-by: prior compiler_referee/spec_auditor reviews cover frozen-source facts and earlier Record/replay candidates; 2026-10-03 compiler-referee delta reviews of the Function descriptor and mixed-row candidate found no blocking/major issues, with minor wording repairs closed; general-component, polarity-specific reverse-addition, and abstract-only contra-meet wording delta reviews found no blocking/major/minor issue; the conditional support-obligation corollary received bounded spec-auditor and compiler_referee review with all findings closed and no remaining finding; the intended-Function necessary-condition subsection received a bounded compiler_referee review with no findings; the conditional Act-family coverage candidate received a bounded compiler-referee review, its minor ownership clarification and major nonempty-fiber premise were repaired, and the delta review closed with no residual finding; the singleton `TypedRow` to candidate Function-support crosswalk received a bounded compiler_referee review with no findings; the abstract-component same-fiber candidate had a major joint-fiber/union-premise finding repaired and its bounded delta review closed with no residual finding; the full witness calculus remains unreviewed
Role-first §8 review: architect pre-write audit; compiler_referee reported one BLOCKING complete-domain-construction gap and major decorated-behavior, entry-role separation, and support-only lifting gaps; spec_auditor found the selected direction conformant and confirmed these obligations remain open. Rigid-hole schema delta: compiler_referee accepted its conditional non-vacuity/actual-preservation claims, while retaining BLOCKING `EnvStore`/`JointWF` construction and a major operational-context-closure obligation. A later bounded Astra theorem audit and Sol architect delta support only the conditional open-graph research candidate below; both retain the domain/construction and closure gaps. The step-index candidate has a bounded compiler-referee audit; the subsequent source-state `spec_auditor` audit requires heap examples to remain conditional until source realization. No carrier insufficiency found.
Implementation authority: none
Supersedes: none; narrows source applicability of structural relation candidates without invalidating their fragment theorems

## 1. Governing semantic decision

The user clarified on 2026-10-03 that Yulang has one basic inequality query,
`A <: B`. Its solver dispatches by endpoint form; this is not a semantic split
into a `Bound` relation followed by a `Compat` relation and a separate cast
relation:

1. `X <: Y` may be stored as a variable edge and propagated transitively.
2. `A <: X` or `X <: B` may be stored as oriented lower/upper payloads of the
   same inequality and propagated or replayed as needed.
3. Concrete `A <: B` is resolved locally. Endpoint-directed resolution may
   structurally decompose it, check optional Record fields, resolve a
   registered cast, or select an adapter. A selected cast or adapter is
   evidence/realization produced while resolving this inequality, not a
   separate semantic relation.

Internal variable edges, lower/upper records, replay routes, phases, and
evidence structures are compatible with this direction. They are solver
machinery for the one inequality judgment, not independent source judgments.
The overall solver is not a transitive concrete subtyping relation: variable
edge propagation may use transitivity, while success of one concrete
resolution cannot be composed with another concrete success to establish a
third inequality.

### User-directed Function effect comparison

Function effect ports are not independent general-`Type` subtype checks. The
user directs the endpoint-dependent `A <: B` solver to represent and resolve
the two effect polarities through effect descriptors:

| Function effect position | Descriptor contents |
|---|---|
| Contravariant | abstract type components plus concrete type components; eligible concrete components may be subtracted, so needed structure may be retained |
| Covariant | abstract type components plus concrete type components in canonical flat form |

Effect expressions need no privileged `body ; tail` syntax. The candidate
representation is polarity-indexed:

```text
E⁺ ::= flat-row{abstract-type-component Aᵢ, concrete-type-component Cⱼ}
E⁻ ::= AbstractMeet{Aᵢ, …, Aₙ}
     | AttachedDescriptor{abstract components, concrete components, attachments}
```

Here `attachments` means references/views into the existing occurrence,
ownership, and directed-weight evidence. It does not prescribe a second
attachment table or independently allocated provenance identity.

Effect variables are a typical abstract component, and concrete effect
records are typical concrete components; neither example exhausts its class.
The admitted interpretation determines the classification, which is not yet
defined as a new source type constructor. These are candidate internal forms,
not syntax. Covariant rows always normalize to a canonical flat form; any
correlation, co-occurrence, original-term identity, or ownership needed after
flattening lives in constraints/evidence, not in a covariant row tree. Thus
`[['a, write], read]` normalizes to `['a, write, read]`, and even a distinct
abstract component in a source nested row does not preserve that tree on the
covariant side.

When a contravariant row contains only abstract components, it may normalize
to their meet, written `[]` (the abstract-component meet, not an empty-effect
value). A row containing any concrete component is not
that meet: it is an attachment-preserving descriptor for reverse addition.
Its structure is retained only as needed to identify how concrete
contributions attach to the abstract components and to one another. For
example, `['a, ['b, write], read]` may keep grouping needed to identify the
attachment to reverse; the correlation and source witnesses remain explicit
in evidence. Collecting common variables is an auxiliary view of abstract
components and does not replace general abstract components or equate
original terms. Co-occurrence consolidation remains distinct from witness
equality.

Contravariant handling is not a total subtraction algebra. “Reverse addition”
is currently only a possible conceptual reading of existing subtraction
evidence, not a new operation or evidence system. A reverse step is justified
only where existing evidence identifies the concrete contribution and its
attachment in the accumulated effect. The frozen directed-stack-weight spec
already carries scoped subtraction identities, ordered push/pop history,
family budgets, residual weights, and the row-split provenance needed by its
own subtraction rule. Do not add parallel attachment/provenance records under
new names. The successor must first show how a proposed reverse step is a
projection/reformulation of that existing evidence, or identify a concrete
missing fact that the existing evidence cannot express. Without that proof,
no reverse step is licensed.

For a concrete Function inequality, compare both descriptors jointly inside
the same inequality resolution. Do not introduce a new tuple of abstract
correspondence, family ownership, attachment, residual, and provenance
fields: the existing coupled interface candidate already carries the shared
assignment, source-owned family identities/incidence, `K,D`, and their
transport. Existing subtraction evidence remains the source for its scoped
push/pop and residual facts. The only additional local evidence needed here
is proof that the polarity-specific row views normalize/transport correctly
and that concrete matching preserves its dependent constraints. Any partial
reverse step must be entailed by the source-supported accumulation and
attachment represented in the existing carriers. If they do not entail that
fact, record the exact missing source fact before adding any representation.
Unmatched contributions remain in their existing correlated
relation/residual context. Neither normalization may silently identify
distinct original terms or detach a concrete component from its context.
No effect port is decomposed as an unrelated `Type` inequality, and the
result of one concrete Function comparison cannot be composed with another
concrete success to establish a third inequality.

The existing directed-stack-weight/effect-subtraction specification is prior
art, not successor authority: its exact `StackWeight`, `SubtractId`, `take(F)`,
`Common(L)`, `K ∩ Common(L)`, `L - J`, W-Mix, replay, and residual-hash-cons
rules must not be imported as successor semantics without the declarative
source proof already required by the effect-design gate. The reuse boundary is:

| Needed fact in a Function inequality | Existing carrier to reuse | Remaining proof question |
|---|---|---|
| Which handler boundary may consume a concrete contribution | Directed left-weight path and scoped `SubtractId` in the old calculus; source handler/activation relation in the coupled-interface candidate | Derive the successor eligibility condition and show the edge/path witness denotes it |
| What was consumed and what remains | Old row-head split `J = H ∩ Common(L)` and residual `L - J`; relational handler image and residual support projection | Prove the mapping from typed concrete row components to `J`, preserving dependent arguments and shared assignment; `H` here is the old calculus's concrete head set, not relational predicate `K` |
| Which symbolic family arguments remain coupled | Existing source-owned `g(o)`, occurrence incidence, shared `ν`, and symbolic `K,D` in the coupled relation | Show a Function effect component occurrence maps to those existing owners; do not add a duplicate ownership map |
| How constraints survive transformation | Existing replay / variance transport and relational reindexing laws | Prove covariant flat normalization and contravariant descriptor construction preserve the same solution fiber |

The genuinely new obligation is the bridge between Function effect-row
syntax/components and those existing carriers. A general abstract component
may denote an entire correlated row view, and a concrete component may
contribute multiple typed request occurrences. Thus neither maps one-to-one
to `g(o)`. The source elaboration must map a component to the appropriate
complete interface under the same `ν`, then identify the occurrence incidence
and directed-weight path/split that account for it. It must prove the old
subtraction evidence denotes the source-supported partial reversal when used
by the single `A <: B` resolver. The directed-weight specification alone does
not supply that theorem.

The coupled-interface candidate defines handler subtraction as residual
support of the full handler image, not set difference: a handled request may
be emitted again by its raw continuation, so the request can remain in the
outward support. The old row split's `L - J` residual is therefore not itself
the semantic proof that a concrete contribution disappears from outward
support. Whenever a proposed reverse step claims that a family/key disappears,
the bridge must establish the corresponding output-absence condition through
the full handler image. A reverse step that recovers some other source
accumulation must be justified by that source rule; it should not be forced
into handler subtraction. If this bridge follows from existing
occurrence/incidence and weight facts, no extra attachment/provenance datum is
needed. If not, identify the exact lost source fact before proposing a field.
Covariant flat-row normalization and the joint two-port Function rule remain
integration proofs; neither licenses a parallel row-subtraction algebra. No
new total cancellation algebra, shared-correspondence map, family-ownership
ledger, or parallel regional/attachment/provenance calculus is proposed.

The intended coupled cases remain:

```text
Fun(a, never, b, c) <: Fun(a, d, [b,d], c)
Fun(a, never, never, b) <: Fun(a, e, e, b)
```

The same target variable `d` remains one shared term across both target ports
under the existing assignment and ownership relation; the source contribution
`b` remains present in the output descriptor. There is
no independent `d <: never` obligation. For the second case, the intended
effect evidence connects target input `e` with target output `e`; whether the
two source `never` spellings elaborate to descriptors with no concrete
contributions is not yet defined. More generally, the descriptor elaboration
of `never` in these examples is open. It must not be obtained from a global
`Never`, `Any`, empty-row, or polarized-sentinel alias. The value-type
meanings of `never` and `Any` remain distinct from the effect descriptor
language; no lattice account is needed for this Function rule. The value
endpoints `a` and `c` remain part of this same Function resolution and its
retained family equations.

This is an endpoint-dependent resolution rule of the single query
`A <: B`; it is not a second effect relation and its successful result cannot
be transitively composed with another concrete Function comparison. Variable
endpoints may retain the same inequality and dispatch through this resolver
when the Function shape is known. The denotation and normalization of
`[b,d]`, descriptor elaboration, subtraction eligibility, variable
correspondence, residual routing, context/Stack preservation, typed-family
transport, and generalization beyond the displayed cases remain proof
obligations. The displayed rules are the user's intended cases; no broader
four-field subtyping rule is approved here.

#### Source-call evidence for the coupling

The coupled shape has a source-level explanation independent of the frozen
Oracle subtype implementation. Under the selected source rules, an ordinary
value parameter has role `Value(a)`. A call reifies the complete argument as
one computation, enters the same receiver activation, forces that carrier at
entry, rebinds its result, and then runs the body. The source continuation
sequences argument execution before the body; if forcing diverges the body
may never run, and if it suspends the body remains its pending suffix. For an
argument computation `D` and body `B`, the source transition has the shape
`Force(D) >>= (v => B(v))`. Bind preserves the ordered trace prefix from `D`
and then the trace from `B` in the post-force configuration. For a fixed
assignment `ν`, collecting over all reachable post-force outcomes gives
`supp(Call(f,D)) ⊆ supp(D) ∪ ⋃_{(v,C₁)∈Force(D)} supp(B(v,C₁))`, where `C₁`
is the live configuration after forcing. If `d` bounds `supp(D)` and `b`
uniformly bounds `supp(B(v,C₁))` over those outcomes for values admitted by
`a`, the call has a combined support bound. If the four-port elaboration maps input descriptor
`d` to that argument bound and maps output descriptor `[b,d]` to the
corresponding combined bound, the first intended inequality has a support-level
justification. This explains why the same contribution may occur in both
positions: it is one carried computation executed at entry, not necessarily
two independent Function fields. The existing source call equation does not
itself prove that `d` has this descriptor meaning. The common value endpoints
`a,c` preserve the argument and result path in this rule.

This source transition explains why an argument effect bound remains
observable through a value-parameter call and why an intended output bound
may need to account for both argument and body execution. It is supporting
source-semantic evidence for the coupling, not the Function descriptor
comparison rule and not an explanation of the input-port meaning or how
effect-position `never` elaborates. The selected source rules for parameter
roles and call entry are in redesign charter §21 and ordinary-computation
package §§3–4.

At the same support-level abstraction, one sufficient explanation of the
second intended inequality would assume that its two effect-position
occurrences of `never` contribute no requests under their respective source
port interpretations, so both target ports may be bounded by the same `e`.
This is a sufficient candidate premise, not a necessary condition on the
approved inequality; another source elaboration could justify it differently.
Value-bottom meaning alone does not establish this premise.
`Result(Value(A)) = Comp(empty,A)` and
`Result(Computation(E,A)) = Comp(E,A)` govern result forwarding; they do not
erase argument or body requests already executed. Both displayed inequalities
remain intended constraints, while this source-call argument only explains
the first conditionally and leaves the `never` elaboration open.

#### Open source-elaboration choice for effect-position `never`

The user-approved inequalities remain the target, and `never` must retain its
value-type identity while `EffectRow([])` and polarized internal bottoms stay
distinct. The following are non-exhaustive research directions, not exclusive
choices or approved semantics:

| Direction | Meaning to define | Consequence |
|---|---|---|
| Uniform component interpretation | Give one source interpretation to the admitted general effect-row component class, mapping each component to the complete interface under `ν` while preserving its type identity | Could derive port behavior without a `never`-specific rule; no inspected source rule currently defines the mapping. Interpreting value-bottom's value set as an empty request set and using that as contra admission would fail to admit an effectful argument, but a computation returning `never` may still emit request prefixes |
| Additional Function-port rule | Only if uniform component interpretation cannot express the approved cases, define a source-derived Function-port mapping without changing the component's value-type identity or aliasing it to an empty row/internal bottom | Requires proof of a source-level distinction independent of spelling-specific Oracle behavior; a special case for the spelling alone would violate the theory-economy gate |

The invariant in either direction is that this is a source denotation question,
not an implementation representation choice. Neither direction authorizes a
lattice account or imports Oracle `is_pure_effect`/materialization behavior.
`Any` remains its own value type and must receive the same uniform component
interpretation unless a separate source distinction is proved.

In the coupled-interface candidate, `ArgDen_A` interprets type-argument tuples
of already established typed request occurrences; `TypedRow(E,ν)` likewise
presupposes `occurrences(E,ν)`. Neither defines how an arbitrary effect-row
component `τ` generates or constrains those occurrences. Thus the component-
to-interface mapping is a genuine missing source rule. Also, `Never` having
no returned values does not imply that a computation typed with result
`Never` has no request prefixes. The source distinction between
`Value(A)` and `Computation(E,A)` must remain visible in any uniform mapping.

#### Existing joint receiver-comparison law

Typed-computation-core §9 already states a sufficient source comparison law
for two descriptions of the same actual callable. At one assignment `ν`, let
`D_i` be the complete admissible challenge domain, including initial
carrier/configuration and future input histories, and let `P_i(d)` describe
the complete joint observations under challenge `d`. Then:

```text
D_checked ⊆ D_actual
∀ d ∈ D_checked: P_actual(d) ⊆ P_checked(d)
```

This law preserves the dependency between argument admission, entry,
continuations, result, and symbolic family observations. It is useful for
testing a proposed Function interpretation, but it does not interpret an
arbitrary row component `τ`, construct either `D_i` or `P_i` from the four
Function ports, or establish either intended inequality. The same section
explicitly leaves finite construction of the complete `ExecuteCallable`
image and higher-order/store challenge relations open. Parameter roles and
source execution rules are already selected; the open point is their mapping
from effect-row components to these complete descriptions.

The existing call equation yields only the support upper bound over all
reachable post-force outcomes. It does not justify an unconditional row-union
equation: a retained receiver can ignore its carrier, while state-dependent
continuations and handler transitions affect the complete image. Accordingly,
one diagnostic lifting candidate was considered:

```text
Cτ(ρ) = ⋃ { Rel_c(ρ) | Γ ⊢ c : Comp(E,τ), for some admitted E }
```

This is conditional notation only: it is defined only if all included
`Rel_c` relations can be transported to one compatible complete-interface
and challenge carrier at the same `ν`. Any capture-avoiding transport must
preserve the source-owned assignment fiber, occurrence incidence, and `K,D`;
otherwise the union is not a valid construction. Even under that premise,
this candidate interprets `τ` as a computation's **result type**. It gives no
source rule relating that result constraint to the effect contribution,
typed-request incidence, or receiver challenge/observation behavior required
of an effect-row component. It does not derive either intended inequality,
and is rejected as an effect-component interpretation.

The failure is local to this candidate. It does not refute every uniform
source interpretation or select a separate Function-port rule. The next
proof must find the source clause that maps a literal component into its
contribution to an existing complete receiver/computation view, derive both
`D` and `P` jointly at the same `ν`, and then check both intended inequalities
against effectful/diverging value-entry arguments, ignored retained
arguments, dependent `K,D`, continuation re-emission, and operation callables
whose native body returns a carrier consumed later by the declared result
interface. No such interpretation or rule is selected by this note.

#### Operation declarations supply only a request-instance subcase

The existing operation-instance rule has a useful, narrower contribution.
Given a resolved operation declaration and substitution `θ`, it constructs
the complete supplied instance
`OpInst(p,θ) = (OpId(p), F<θ(ρfamily)>, Aθ, Bθ, Λθ)`. Once a typed request
occurrence exists, its payload, continuation, symbolic predicates, and
incidence remain attached; `OpCompat` compares that retained instance with a
handler arm. The ordinary source operation rule also gives the concrete
emission path: invocation constructs a request thunk, and a source-demanded
force emits the request. None of these rules turns a row component into a
request occurrence.

The stable-core example declares `act tick 'a` with `ping: 'a -> 'a` and
contains a callable signature with bracket-arrow effect slot `[tick 'a; 'e]`.
The signature manifest expects `box('a & 'b, 'c) -> ('c -> ['b] 'c) ->
['b, 'a] ()` and rejects `tick` in the output. This is source/signature
evidence that an Act-family application and an abstract component occur in
one effect slot; it is not a semantic rule mapping either item into a
complete receiver interface. The fixture uses bare `BracketRow`, not the
separate apostrophe-prefixed standalone `EffectRowType` form `'[...]`.
Authoritative BracketRow grammar explicitly leaves use-site wiring to HIR /
lowering / inference out of scope. Standalone `EffectRowType` authority
likewise leaves open/closed classification, row-tail meaning, inference, and
annotation lowering outside syntax scope. Neither syntax authority lets a
semicolon or final variable decide tail meaning.

Thus the existing source theory can describe an Act request **after** its
declaration and instance are supplied, and can describe how execution emits
one. It still lacks the annotation clause that resolves an Act-family row
component to a permitted request/interface contribution, as well as the rule
for an abstract component such as `'e` to denote a correlated interface view
under `ν`. It also has not classified every admitted TypeExpression as an
effect component. The next semantic gate is to derive that annotation clause
for resolved Act applications together with abstract components, then state
whether the derivation is restricted to that fragment or extends uniformly
to every admitted component. This is research only; it adds no occurrence,
ownership, or provenance carrier and does not select a semicolon-tail model.

#### Candidate family coverage clause, with the remaining boundary explicit

The smallest candidate for a resolved concrete family item treats it as a
coverage predicate on an already established typed request, not as a request
constructor. For `τ = F(α₁,…,αₙ)`, one possible row-support projection at a
fixed `ν` is

```text
FamilyAllowed_τ(ν,q) iff
  family(q) = F ∧ family_args(q) ≈ (ν(α₁),…,ν(αₙ)).
```

The comparison uses the source-prescribed invariant family relation. It sees
only the family projection of `q`: the complete request keeps its operation
path, operation-local witnesses, payload, response, raw continuation, and
shared `K,D` associated with its existing `OpInst`; execution constructs the
live continuation while retaining that instance. Thus two requests with the
same family point remain distinct in the complete view even if this support
predicate treats them alike. This is a candidate coverage rule for resolved
Act-family items, not a theorem that the source annotation already has this
meaning.

This candidate has a conditional derivation from the coupled-interface draft's
`TypedRow` projection. If source elaboration maps the singleton annotation
component `τ` to one owned occurrence `oτ` with `head(oτ)=F` and
`ν(g(oτ))=(ν(α₁),…,ν(αₙ))`, and the assigned tuple satisfies
`ν(g(oτ)) ∈ ArgDen_A(oτ,ν)` (so `J_{ {τ} }(ν) ≠ ∅`), then
`TypedRow({τ},ν)={(F,(ν(α₁),…,ν(αₙ)))}` and `FamilyAllowed_τ` is precisely
membership in that support point. This is only a conditional pointwise
calculation: the premise that an annotation component supplies `oτ` is the
missing source clause. It does not identify `oτ` with a dynamic request event
or with the request's operation-local witness.

Under the separate coupled-interface draft's unselected Function-contract
candidate, every immediate request in every complete call observation must
belong to `TypedRow(E,ν)`. With the singleton mapping and nonempty-fiber
premise above, that support obligation reduces to requiring the request's
family point to equal `(F,(ν(α₁),…,ν(αₙ)))`. This composes the conditional
point calculation with an existing candidate complete-call rule; it does not
establish the annotation-to-occurrence mapping, the candidate Function
contract's authority, or any concrete port comparison.

For an abstract component `α`, the corresponding candidate cannot be a
family-point predicate. Its contribution must be the existing complete-view
constraint denoted by `α` under the same `ν`, preserving its source-owned
incidence and shared `K,D`. An abstract component may therefore constrain
multiple request families and their dependent values jointly. This notation
does not define the component's denotation, its nonempty-fiber condition, or
how it combines with a concrete component.

The only conclusion licensed by §9 is conditional: if both component views
and the complete challenge/observation carrier are supplied independently,
and every checked observation satisfies their combined allowance, complete
observation inclusion transports that obligation to actual observations at
the checked challenges. It does not establish the allowance or its
combination. The candidate does, however, expose the minimum no-duplication
shape: preserve the annotation's typed path to its existing complete port,
project concrete family coverage from existing requests, and leave all
request-specific data in the existing complete relation. It introduces no
new region, attachment, occurrence, or provenance ledger.

The current source rules support the order `OpInst` / demanded execution /
complete request view. They do not support the reverse implication from an
annotation component to `FamilyAllowed`, and do not yet give the abstract
component rule. The fragment-vs-uniform question remains open, as does whether
the candidate family predicate is the intended source contract. It cannot
yet be used to derive either intended Function inequality.

#### Candidate abstract component as a same-fiber view

For an abstract component, the only currently supported reuse shape is a
projection of the existing complete relation `Rel_C(ρ)` to the effect port
identified by the source typed path. At fixed `ν`, this keeps the component's
complete view and every dependent root/request/continuation in the same
`Rel_C` fiber. Its support projection may contain several family points; the
family support alone is not the component denotation. `K,D` stay in the
complete relation and are not copied into an abstract-row side table.

The following support equality is proposed only conditionally. Assume that
source elaboration maps an abstract component `α` to such a port projection
`View_α(ν)` and derives the family point `pτ(ν)` for a resolved concrete
component `τ`. Also require a nonempty jointly admissible `Rel_C` fiber at
`ν`, retaining shared `K,D` and both components' dependencies, and a
source-derived component-combination rule whose support coordinate is the
union of its component occurrences. Compute both `Support(View_α(ν))` and
`pτ(ν)` in that retained joint context. Only under these premises does the
proposed flat covariant support view satisfy

```text
Support_E(ν) = Support(View_α(ν)) ∪ {pτ(ν)}.
```

Separate component mappings alone do not entail this equality. This is only
the support projection. The accepted complete relation must
still retain the shared assignment and correlations of `View_α`; independently
projecting `View_α` and then taking a Cartesian product with the concrete
point would admit fibers that never existed jointly. Deduplicating equal
support points likewise does not identify their original component terms or
discard their separate incidence. The formula therefore predicts no new
ownership or provenance structure: source identities and dependencies stay
where the existing `Rel_C` / `K,D` representation keeps them.

No source rule yet maps `α` to that port projection or defines its fiber,
nonemptiness, component combination, or typed-path transport. Nor is the
support union a handler-subtraction or contravariant reverse-addition rule.
This is a reuse-shaped candidate for the abstract component, not its selected
denotation or a derivation of `[b,d]` / shared-`e`.

The compact signature `'a ['b, write int] -> ['b] int` places `'a` in the
value-input position and shares effect variable `'b` between input and result
descriptors. `write int` is subtractive in the contravariant descriptor;
removing it requires concrete-family match evidence and its type-argument
equations, while the shared `'b` survives in the result descriptor. This
fixes the intended notation, not the equality semantics of co-occurrence
merging or a complete subtraction algorithm.

#### Conditional support obligation inside complete comparison

This is a conditional corollary, not an annotation meaning or acceptance rule.
Fix a jointly satisfiable assignment `ν`, retained shared `K,D`, compatible
complete challenge/observation carriers, a checked challenge `h`, and one
supplied request-support projection `Qν` at the same source-defined boundary
on both sides. Assume:

```text
D_checked(ν) ⊆ D_actual(ν)

∀h ∈ D_checked(ν):
    P_actual(ν,h) ⊆ P_checked(ν,h)
```

If independently supplied component denotations define
`Allowed(ν,h,O,q)`, and every checked observation satisfies that predicate
for each request in its support,

```text
∀h ∈ D_checked(ν), ∀O ∈ P_checked(ν,h), ∀q ∈ Qν(O):
    Allowed(ν,h,O,q),
```

then the same support obligation holds for every actual observation at each
checked challenge:

```text
∀h ∈ D_checked(ν), ∀O ∈ P_actual(ν,h), ∀q ∈ Qν(O):
    Allowed(ν,h,O,q).
```

The proof is only set inclusion: each actual observation belongs to the
checked observation set. Actual execution coverage additionally assumes the
actual behavior is represented in `P_actual`. The domain premise makes
checked challenges admissible; it gives no conclusion for actual-only
challenges. Empty challenge/observation sets make the formulas vacuous and do
not establish nonempty typed-row fibers.

This corollary requires `Allowed` and each component view to be supplied
independently of the observations being checked, under the same `ν` and joint
`K,D`; otherwise it can become tautological or combine incompatible fibers.
For a concrete family item, coverage must be a supplied predicate over
already established typed requests, using the full family tuple and source
family relation. It constructs no request or operation instance. An abstract
component's correlated view and any challenge/observation dependence of
`Allowed` must likewise be supplied. `Qν` must observe the same complete
source boundary on both sides, including the relevant finite prefixes,
designated result consumption, and future/resumption behavior represented by
the supplied challenges and observations.

Support inclusion is only a necessary projection inside the complete §9
comparison. It cannot reconstruct `P_checked`, prove challenge-domain
inclusion, validate annotation acceptance, discharge `OpCompat` or handler
eligibility, or establish that the supplied component denotations are source
meaning. `OpCompat` continues to retain operation-local binders,
payload/response, profiles and continuation obligations. This argument uses
neither `Filterφ` nor the row residual `L - J`; it entails no observation
deletion, subtraction, accumulation law, or concrete-success composition.
Neither intended Function inequality follows. The first still needs the
negative-port interpretation and the meanings of `d` and `[b,d]`; the second
also needs the meanings of both effect-position `never` occurrences.

#### Necessary conditions from the intended Function cases

The following are constraints on a derivation that uses the sufficient §9
complete-comparison law; the approved inequalities do not prove that every
successful adaptation must use this particular proof route. Any alternative
source realization needs its own preservation argument.

For

```text
Fun(a, never, b, c) <: Fun(a, d, [b,d], c)
```

assume a checked challenge `h` is admitted by `d` and carries a nonempty typed
request observation at the designated argument boundary. If the actual
negative `never` endpoint were interpreted as permitting only request-free
incoming carriers, that same `h` would be absent from `D_actual`, contrary to
`D_checked ⊆ D_actual`. The discriminator requires an actual admitted
challenge: a nonempty upper-bound descriptor `d` alone does not establish one.
A request prefix emitted before divergence still witnesses the challenge;
divergence before any request does not. This excludes a pure-only admission
reading of the actual negative `never` endpoint in this case. It does not
equate `never` with an empty row or internal bottom, nor does it select the
endpoint's successor meaning.

For each admitted checked challenge, the output interpretation of `[b,d]`
must contain the actual complete observations admitted by §9's comparison.
For value entry `Force(D) >>= B`, request support has the conditional upper
bound

```text
supp(Call(f,D)) ⊆ supp(D)
  ∪ ⋃ { supp(B(v,C₁)) | (v,C₁) is reachable after Force(D) }.
```

Thus if `d` bounds the argument and `b` uniformly bounds the body at every
reachable post-force state, a candidate `[b,d]` must cover those actual
requests and keep their shared constraints. This is an upper bound, not an
exact row-union equation. An argument may diverge before the body runs;
retained computation parameters may be ignored; shallow handlers may consume
requests or forward/re-emit them through the raw continuation; and designated
result consumption can expose a returned carrier. The complete image decides
which observations remain. Support inclusion alone does not cover returned
values, latent interfaces, stores, or resumption histories.

For

```text
Fun(a, never, never, b) <: Fun(a, e, e, b)
```

both target ports refer to the same term in one assignment `ν`. Any family,
value, request, continuation, or residual constraints incident to that term
must remain in the shared `K,D` fiber while constructing challenge and
observation views. Independent port marginals could choose incompatible
assignments to `e` and pass separate projected checks without a joint
comparison witness. Sharing the term does not equate events or require exact
input/output support equality; the complete source image determines how entry,
handling, and resumption relate them. Neither occurrence of effect-position
`never` receives a meaning from this argument.

These conditions narrow the next component-denotation rule: it must establish
challenge admission for an effectful checked carrier, preserve the actual
argument prefix and body/result observations in one joint output view, and
retain the shared assignment for linked ports. They establish no `[b,d]`
normalization, component classification, concrete reversal, or complete
Function inequality. No new evidence carrier or effect algebra follows.

Frozen-source characterization supports the coupling but does not define its
successor meaning. `infer/.../propagate.rs` detects a negative `Neg::Bot`
argument effect and routes both the target argument effect and source return
effect to the target return effect. The frozen specialization `TypeGraph`
instead decomposes independent Function components; for pure callee/cast
fixtures it reaches `EffectRow([]) <: Never`, which current code happens to
accept through a fallback. That fallback is not authority for the intended
rule and must not be used as its semantic explanation.

The frozen inference branch is specifically: when the lower Function's
argument-effect endpoint is `Neg::Bot`, enqueue the upper argument effect
below the upper return effect (after stripping target-return Stack wrappers)
and enqueue the lower return effect below that same upper return effect. This
is evidence for coupled effect flow. It does not yet prove that the source
algorithm implements the exact user rule for arbitrary `b,d`, because the
source code constrains two contributions into a target effect endpoint while
the rule writes their combination as `[b,d]`. Their equivalence, join/row
normalization, shared-witness transport, and Stack behavior remain explicit
proof obligations. The frozen specialization's four-child decomposition is
not a valid successor rule for this branch.

Optional Record comparisons are the discriminator. Oracle accepts each of

```text
{} <: {foo?: string}
{foo?: string} <: {}
{} <: {foo?: int}
```

and accepts the chain

```text
{} <: {foo?: string} <: {} <: {foo?: int}
```

while rejecting the direct comparison

```text
{foo?: string} <: {foo?: int}
```

Therefore the endpoint-dependent inequality solver cannot transitively
compose concrete resolution successes. Optional Record checking is a local
rule for resolving a concrete inequality; it must not be added to a global
structural relation and transitively saturated.

The examples are user-supplied Oracle observations, not new successor source
fixtures or a complete operational account of the evidence. They do not
yet determine which fields are materialized, dropped, defaulted, or converted;
whether a concrete adapter is required at each site; or how ambiguous
adaptation is selected.

## 2. Candidate endpoint-dependent solver organization

Use one comparison entry with its source context, endpoint pair, and the
consumer/source identity to which evidence will attach:

```text
Gamma; j |- A <: B  ==>  unresolved | success(evidence) | failure
```

`j` retains the originating source boundary, lexical openings, shared
declaration/request witnesses, typed evidence and joint symbolic coordinates.
The result records whether resolution only checked the endpoints, selected a
cast/adapter, or constructed executable realization. These are outcomes of
solving `A <: B`, not additional input relations.

The endpoint-directed transitions below are an unapproved solver candidate:

| Endpoints | Internal solver work |
|---|---|
| `X <: Y` | retain an oriented variable-edge record and propagate variable-bound information transitively, carrying source and guard context |
| `A <: X` | retain a lower-payload record for the unresolved inequality at `X`; move it along admitted variable edges |
| `X <: B` | retain an upper-payload record for the unresolved inequality at `X`; move it along admitted variable edges |
| concrete `A <: B` | resolve locally by structural decomposition, optional Record checks, registered cast resolution, or adapter resolution; attach child results/evidence to this query |

The frozen Oracle maps those endpoint forms to the listed lower/upper
orientations. When payloads share a pivot, the frozen machine can prepare a
replay query; its builders select eligible routes, retain the pivot and both
record identities, and compose inherited weights. They do not enqueue every
raw same-pivot pair. Lower insertion can also use an incremental row-residual
route. This is characterization of internal solving machinery, not a
successor semantic rule.

If source preservation admits a replay, it creates another inequality task
`A <: B` with the two payload records, shared pivot and inherited guards
attached as derivation data. The same endpoint dispatcher resolves it. The
exact source condition for creating that task remains open: same-pivot
coexistence and two independently successful endpoint resolutions do not by
themselves authorize it. Until the source bridge proves a replay mandatory,
failure of a candidate replay does not prove that the original source
constraints are unsatisfiable.

Keep original source comparison tasks and generated replay tasks separately
identified. An unresolved task can be suspended and resumed under the same
context after endpoint substitution. Variable reachability alone cannot
invent a new comparison task. Every original or replay-derived task re-enters
the selected generation-time scope guard before committing specialization.
The source-preservation and conversion-placement rules remain open.

Successful concrete resolution and its cast/adapter evidence stay attached to
their own source or generated task. They do not become variable edges or
premises for a third concrete comparison. In particular, success of `A <: B`
and `B <: C` does not discharge `A <: C`; the latter query must be resolved
directly if it is a source obligation. A replay query, if independently
justified, is likewise resolved afresh. Optional Record behavior supplies the
concrete witness to this non-composition requirement:

```text
{foo?: string} <: {}          succeeds
{} <: {foo?: int}             succeeds
{foo?: string} <: {foo?: int} fails
```

The `X = {}` example also shows why lower/upper storage must not be
misinterpreted as two successful concrete checks whose results compose. It
does not settle whether a source-preserving solver requires replay for any
specific pair; that is a separate proof obligation.

The index `j` stands for the originating source boundary, lexical opening,
retained typed evidence and applicable scope context. Every derived task still
passes the selected generation-time scope guard before resolution. This is a
candidate algorithmic organization, not a chosen data structure or a proof
that all source sites generate finitely many contexts.

For unresolved or variable endpoints, the solver may suspend the same
inequality task. Its endpoints, context and eventual resolution evidence must
remain correlated through aliases, replay, generalization and SCC intrusion.
The candidate mechanism and its finiteness are open.

## 3. Relation to reviewed structural results

The following results remain valid within their declared mathematical
fragments:

- `2026-10-03-scoped-structural-projection.md` proves properties of a
  transitive greatest structural simulation over mandatory Records,
  Functions and declared-variance constructors. Its theorem does not model
  local cast/adaptation resolution or optional Record fields.
- `2026-10-03-scoped-constraint-solving.md` decides closed comparisons in
  that same structural fragment. Its regular equality quotient and permission
  propagation remain separately useful, provided adaptation compatibility
  does not stand for `Eq`.
- `2026-10-03-open-residual-factorization.md` proves a conditional
  factorization for bounds interpreted in the greatest structural relation.
  Its pair normalization and §4.1 equivalence cannot be applied to general
  concrete compatibility until preservation of both compatibility and
  conversion evidence is proved.
- `2026-10-02-typed-boundary-realization-draft.md` gives a conditional
  operational realization for fixed-shape Function/Thunk adapters. It is not
  a general concrete-compatibility oracle and does not cover optional Records.

These fragment theorems are not refuted. Their source applicability is
narrower than treating their `<=` as the one relation used at every concrete
boundary.

## 4. Current source evidence and limits

The current successor solver represents polarized Function terms and
variable bounds, but its term algebra has no Record or cast/adapter node:
`crates/yu-solver/src/term.rs::TermView` and
`crates/yu-solver/src/lib.rs::InferenceSession::constrain_live` are the
owning comparison surface. Closed types in `crates/yu-types/src/lib.rs`
likewise have no Record or adapter constructor. This is research/feasibility
evidence; the current task still authorizes no compiler implementation.

The successor HIR does not admit cast declarations into its resolved
expression envelope (`crates/yu-hir/src/module.rs`). The parser owns
`cast` declarations, and the stable-core example
`tests/contracts/stable-core/v0/run/vm/pass/example_cast/main.yu` demonstrates
implicit value casts in that contract corpus. The typed-computation design
also records frozen evidence for registered field casts, while explicitly
not establishing general whole-Record adaptation.

The frozen Oracle implementation has two distinct routes that a successor
could place behind one compatibility interface, but they should not be
conflated as existing evidence of one adapter mechanism:

- For Record-to-Record constraints,
  `a58eefc3:crates/infer/src/constraints/machine/propagate.rs` visits upper
  fields in `enqueue_record_fields`, skips absent lower fields, skips the
  lower-optional/upper-required case, and otherwise emits a field-type
  comparison. Frozen specialization separately rejects a missing *required*
  upper field and recursively checks matching fields at
  `a58eefc3:crates/specialize/src/specialize2/type_graph.rs`.
- For different nominal constructor paths, constraint propagation emits
  `NominalCastNeeded`. `AnalysisSession::constrain_nominal_cast` eagerly adds
  constraints for exact-path cast candidates; eligible source-boundary
  diagnostics later use `CastTable::resolve_value` to classify missing,
  unique, or ambiguous candidates. This route is implemented in the frozen
  `crates/infer/src/analysis/session/{generalize,ocast_activation}.rs` and
  `crates/infer/src/casts.rs`.

Consequently the optional-Record examples do not show that Oracle routes those
checks through its registered nominal cast table. They show why successor
concrete compatibility cannot be the transitive closure of every local
structural/adaptation success. The user-selected direction remains to
investigate one local compatibility/adaptation boundary; a candidate resolver
may dispatch to Record adaptation and nominal cast rules while retaining
distinct derivations and evidence. Whether that unification is sound and
operationally faithful is open; it must not silently turn Record checking into
registered nominal casts or compose boundary successes.

The frozen specialization and runtime paths add a useful boundary distinction.
`specialize2/task_solver.rs` reconstructs materialized actual/expected pairs
for expression consumption, function-body checking and computed definition
signatures, then sends those pairs to `TypeGraph::constrain_materialized_subtype`.
That entrypoint interns an individual source-derived comparison with provenance;
`TypeGraph::process_subtype` propagates variable-to-variable comparisons as
edges and stores variable-to-concrete comparisons as bounds, while concrete
Record pairs take the local field/presence branch described above. This is
evidence for rechecking concrete boundaries during specialization rather than
assuming that a propagation skip permanently discharged them. It does not
prove how every original inference obligation is transported, nor authorize
the successor to reproduce this implementation topology.

The frozen inference machine also explicitly combines lower and upper bounds
stored on one variable. In `crates/infer/src/constraints/machine/bounds.rs`,
`cpk_lower_bound_replay_actions` pairs a newly added lower bound with existing
upper records; `cpk_upper_bound_replay_actions` performs the symmetric
pairing. Eligible pair replay actions carry the endpoint comparison,
`BinaryReplayDerivation { pivot, lower, upper, rule }`, and replay claim
parents. Prepared route evidence selects the ordinary pair; lower insertion
may instead use a row-residual route. A selected action can be trivial,
duplicate or evidence-only and be prefiltered from new worklist execution.
Thus Oracle has a bound-derived concrete comparison route in addition to
direct source-derived boundaries. This is narrower than closing all
successful concrete comparisons transitively, but the successor proof must
establish why each replay task follows from the originating inequalities.
The frozen derivation records lower/upper payload parents; it does not by
itself locate the runtime expression boundary where a resulting conversion
should execute.

Runtime realization is also split across paths. In the frozen
`crates/mono/src/boundary.rs`, Record boundary support checks required-field
presence and recursively asks whether shared field boundaries are supported;
it does not select nominal cast rules. The emitted generic `Coerce` for
`RecordFields` is lowered by `crates/evidence-vm/src/runtime.rs` to an alias,
so that node alone does not materialize a Record adapter. Separately, the
Evidence VM's `adapt_value_result` has a Record branch which calls
`adapt_record_value_result`: when that adapter branch is reached after the
runtime-equivalence shortcut, it visits target fields, omits a target-optional
field absent from the source shape, recursively adapts matching field values,
and reconstructs the target Record (extra source fields are not copied on this
path), except that source-Thunk to non-Thunk field boundaries retain the value
without recursive adaptation. Missing runtime values for declared matching
fields fail. This recursive adapter does not dispatch registered nominal
casts for child `Con` pairs.
An earlier directional runtime-equivalence shortcut can return the original
Record unchanged, preserving extra fields; rebuilding is therefore not an
invariant of every successful Record boundary. The older mono runtime also
returns Record values unchanged for supported Record boundaries, unlike the
Evidence VM adapter path.
Explicit Record literals can instead consume a field under its expected type
and materialize a direct nominal cast there; spreads and width changes remain
on the whole-Record boundary path. The frozen system therefore has reusable
local structural adapters and registered nominal casts, but not one shared
runtime resolution mechanism. A common successor inequality solver is a plausible entrypoint whose
concrete endpoint branch distinguishes a supported shape check from selected
conversion evidence and from an adapter actually emitted. In particular, source acceptance, identity preservation versus
projection, missing-field behavior and nested registered-cast realization
remain path- and stage-dependent questions.

The frozen nominal-cast route is not yet a uniform resolver either:
`TypeGraph::constrain_direct_cast` adds constraints for every exact-path Value
cast candidate, while specialization emission's `direct_cast_rule` selects the
first exact-path match. The separate `CastTable::resolve_value` API classifies
missing, unique and ambiguous cases. Any successor unification must decide
which stage resolves candidates and retain that decision with the originating
boundary; the historical paths are evidence for the problem shape, not an
approved policy to copy.

Successor named-Record type syntax currently requires `name: Type` fields;
the optional Record pattern syntax concerns pattern defaults and named
arguments, not optional fields in type declarations. Thus the user's
optional-Record observations are a semantic constraint on the successor
design, not evidence that this branch already parses or implements those
types.

## 5. Candidate Record-local checking derivation

The frozen concrete Record checker suggests a local presence-and-child
derivation for closed shapes. This is a candidate compatibility rule, not an
adopted source rule or a runtime adapter specification:

| Lower/actual field | Upper/expected field | Inference propagation | Concrete validation |
|---|---|---|---|
| absent | optional | no child comparison | absence is permitted |
| absent | required | no child comparison | reject missing required field |
| present, required | absent | no comparison | ignore extra lower field |
| present, optional | absent | no comparison | ignore extra lower field |
| present, required | present, optional | compare field types | validate child comparison |
| present, required | present, required | compare field types | validate child comparison |
| present, optional | present, optional | compare field types | validate child comparison |
| present, optional | present, required | defer the child comparison | validate child comparison; source-level acceptance and runtime presence guarantee remain unverified |

The last row matters: propagation skips the optional-to-required child pair,
but concrete specialization still checks matching field types. That skip is
not a permanent success. For the user-supplied discriminator, empty-to-optional
uses permitted absence, optional-to-empty has no upper fields to inspect, and
optional-string-to-optional-int reaches the incompatible child comparison.
This matches the stated pairwise outcomes as endpoint-specific inequality
resolution without adding optional Records to a transitive structural relation.

A candidate local derivation is:

```text
ResolveRecordInequality_j(L, R)
  = required-upper-name checks
    + one child inequality L.label <: R.label for each shared label
```

Its evidence retains the original boundary, label correspondence, permitted
absence, ignored extra fields, deferred child obligations and every child
compatibility/conversion result. The inequality solver's concrete endpoint branch could return distinct tagged
derivations for Record checks, ordinary structural checks and exact-path
nominal cast resolution while preserving one boundary context. At a shared
Record field it creates a child inequality task under the same solver entry,
allowing a registered conversion only when that child pair independently
resolves. This is a candidate rule shape; it does not identify checking
evidence with an executable whole-Record adapter, nor show that Oracle routes
optional Record comparisons through its nominal cast table.

Executable Record realization remains a separate gate. In particular, evidence
is still missing for how omitted fields, extra fields and optional-to-required
fields behave at runtime, and whether a selected field adapter can be embedded
in an aggregate adapter. No composition law may be inferred from successful
boundary checks.

### 5.1 Candidate concrete endpoint branch of the inequality solver

The user's requested direction is one inequality solver whose concrete
endpoint branch dispatches to structural checks, Record rules, registered cast
resolution or adapter resolution, with tagged derivations and realization
evidence. These are solver steps and outcomes for `A <: B`, not separate
semantic judgments or an adapter relation chained after compatibility. This
does not claim that optional Records use the registered nominal-cast table, or
that the frozen routes already share an implementation. This is a documentary
candidate only.

```text
InequalityTask_j = {
  boundary_or_replay_id,
  actual,
  expected,
  scope_guard,
  retained_typed_context
}

InequalityOutcome_j =
    Suspended { dependencies }
  | Rejected { reason, resolution_evidence }
  | Accepted {
      resolution_evidence,
      realization_evidence
    }

resolution_evidence =
    StructuralCheck
  | RecordCheck { presence, shared_field_inequality_tasks, ignored_extras }
  | RegisteredCastResolution { candidate_resolution }
  | AdapterResolution { plan }

realization_evidence =
    Unresolved
  | ProvenIdentity
  | GenericAdapterPlan { child_evidence, runtime_requirements }
  | SelectedNominalCast { rule, instantiated_constraints }
```

The names above are placeholders for separate evidence kinds, not source rules.
In particular, `ProvenIdentity` requires an independent source/runtime proof;
it cannot be inferred merely from `Accepted`. A resolver result also does not
show that an operation was emitted. A separate execution correspondence must
connect query identity, selected evidence, consumer boundary and emitted
operation. Different boundary contexts sharing the same endpoint pair must
remain distinguishable, while variable-bound replay remains the only source
of generated replay queries.

For a Record inequality, the outer `RecordCheck` records presence/extra-field
facts and issues a child inequality task for each shared field. A child
nominal cast may supply child selection evidence, but an aggregate adapter
cannot be constructed from those successes until runtime composition is
specified and proved. Likewise, two accepted local queries never entail a
third query: check evidence stays attached to its own boundary or replay id
and never becomes a concrete reachability edge.

This shape gives one inequality-solving entry where endpoint rules can invoke
structural checking, Record adaptation planning, and nominal cast resolution,
while keeping check success, candidate selection, adapter planning, and
execution as evidence stages of that same query. It does not
settle optional-to-required acceptance or presence guarantees, omitted/extra
field realization, cast ambiguity or selection timing, nested casts, effects,
or the location where replay evidence executes. The existing gate remains
bound-replay conservation first, followed by selection/conversion preservation
and executable realization; this dispatcher cannot shortcut those proofs.

## 6. Next theorem gate: inequality-task conservation

Do not extend structural residual normalization yet. The source judgment is one
inequality `A <: B` with endpoint-dependent solver rules. First prove that the
internal solver transitions preserve the source comparison ledger in both
directions for a fixed finite source elaboration. Each original inequality
task retains its identity, ordered endpoints, scope context, symbolic
coordinates and consumer. Each replay-generated inequality task retains its
pivot, lower/upper record identities and inherited guard/context.

Under one admissible shared assignment, variable-edge propagation may use
transitivity. Lower/upper records are internal indexes of unresolved inequality
tasks. A selected replay is another inequality task; its source derivation must show
why that task is required.
The conservation proof must show that no original guarded task is lost, every
mandatory replay is generated or represented by an identified row/residual
route, and no extra rejecting task is introduced. Each task re-enters the same
endpoint-dependent solver. Concrete resolution outcomes and cast/adapter
evidence remain attached to their task and are never premises for a third
concrete comparison. This is a target statement, not an established theorem.

The first proof fragment can fix closed Record shapes and treat nominal cast
resolution as a tagged solver outcome. It should preserve distinct contexts
for equal endpoint pairs, recheck scope guards on generated tasks, and connect
replay parents to the actual consumer boundary for any emitted conversion.
Same-pivot presence alone does not prove replay admission. Frozen proof
coverage and queue policy are characterization evidence, not source criteria.
Finite provenance and source-wide context closure remain premises to prove.

After task conservation, prove that concrete endpoint resolution retains
selected check/cast outcomes and realization evidence without composing
independent successes. Then extend residual factorization to preserve equality,
original inequality provenance and joint symbolic coordinates under one
assignment. Effectful interfaces, unknown Record shapes, lifecycle, and
implementation remain open. No optional-Record grammar, acceptance surface,
conversion-selection policy, resource limit, or implementation representation
is approved here.

## 7. User clarification: role-first Function elaboration (2026-10-03)

The user reordered the immediate source-semantic gate. Do not begin from a
uniform map from an effect-row component `τ` to a complete receiver/computation
interface. First derive:

```text
function literal + expected context
  -> receiver role (pure / handler)
  -> Function interface elaboration
  -> effect-port interpretation
```

The intended source rules are: an ordinary unannotated function literal
infers as pure; an explicitly annotated Function boundary is a handler
boundary; a function literal in callback position receives handler role from
its expected context. The role is selected by source introduction/context,
not reconstructed from effect-port syntax. This is a distinct axis from
charter §21's parameter-entry role (`Value` versus `Computation`). Preserve
§21's entry rules.

The existing source packages establish every function's computation-receiving
invocation, inert whole-argument reification, entry force/rebinding for value
parameters, retained computation parameters, and result forwarding. They do
not yet derive the new pure/handler literal-role rules, explicit annotation
boundary elaboration, or expected-context propagation for callback literals.
That missing source Function annotation/context elaboration is the owner of
the next derivation gate. It precedes both effect-port interpretation and any
general component-to-`Rel_C` mapping.

For the intended callback lift

```text
Fun(a, never, b, c) <: Fun(a, d, [b,d], c)
```

the source operational motivation is the handler-capable callback's actual
entry sequence `Force(D) >>= B`: a request exposed while forcing the argument
remains in the complete invocation, and the body executes in each reached
post-force state. Thus a joint output interface may need to account for both
argument computation `d` and body effect `b`. This is conditional motivation,
not yet a derivation of the inequality: the source elaboration must define the
actual and checked complete domains, typed paths, effect-port views, and the
joint `[b,d]` composition under the same `Rel_C` fiber and `ν`. Do not derive
it using four independent general-Type port comparisons.

Keep value `never`, empty effect row, and polarized solver bottom/top
distinct. No effect-position special meaning for `never` follows. Existing
`Rel_C`, occurrence/incidence, shared `K,D`, directed-weight and subtraction
evidence remain the candidate proof substrate. “Reverse addition” remains a
possible conceptual reformulation of already witnessed partial subtraction;
do not duplicate regional, attachment, or provenance machinery. Add a
representation only if a concrete source fact required by role-first
elaboration is shown to be inexpressible by the existing evidence.

Consequently, earlier notes that made a uniform component interpretation the
first gate or left a user choice between “complete-view bound” and “additional
contribution” are superseded as research order. Those questions may remain
downstream, but only after role-specific Function interface elaboration shows
that a component bridge is still needed. This addendum records the user's
direction; it does not claim the missing elaboration or inequality proof is
complete and grants no implementation authority.

## 8. Role-directed elaboration proof obligations (2026-10-03)

The bounded source derivation and independent compiler/specification review
confirm the role-first ordering, while exposing the exact proof boundary.
Charter §§16–21 and core §§6–9 already supply common invocation, inert
argument reification, parameter entry, typed result forwarding, and conditional
complete-domain comparison. They do not construct the receiver-role-indexed
Function interface or its complete challenge domain from a source literal or
expected callback context.

| Source case | Selected receiver role | Required elaboration obligation |
|---|---|---|
| Unannotated literal in synthesis | Pure | Synthesize the body/result using §18 and the parameter entry fixed by §21; construct the complete Function view without identifying “pure” with empty call support. |
| Explicitly Function-annotated literal | Handler boundary | Preserve the original annotation occurrence and construct its source boundary/profile and typed paths before interpreting effect ports; the annotation does not invent operation arms. |
| Literal checked in callback position | Handler from expected context | Elaborate against the expected callback boundary while retaining its actual source entry and body; expected context cannot infer parameter retention from an effect row. |
| Already-constructed function value checked at a handler-capable interface | Comparison/adaptation case, not literal introduction | Preserve actual executable entry and original decorated behavior. A changed entry or boundary requires a separately justified executable conversion. |

Receiver role and parameter entry are independent axes. Every case must be
parameterized by §21's `Value(A)` entry (receive, force once, rebind) or
`Computation(E,A)` entry (receive, retain); neither role nor solved effect
support changes that choice. Thus `Force(D) >>= B` is an operational premise
only for a value-entry case. For retained entry, the complete invocation
depends on actual body consumers: it may ignore the carrier or consume it
through an explicit source path. Empty effect support cannot decide between
these cases because pure divergence remains observable.

The construction of the complete source domains must be independent of the
comparison's success and of the set of currently observed calls. It must not
make an unused exported function pass by vacuity, nor quantify over arbitrary
machine configurations that no source context can construct. It must cover
source-admissible caller histories, live stores, supplied values/computation
carriers, responses, callback/future-use paths, and resumption. The existing
coupled relation is the semantic candidate; an effective finite presentation
is a later proof obligation. An empty joint fiber is not evidence of
acceptance.

For a value-entry call with argument computation `D`, the bind law gives the
conditional execution shape:

```text
actual receiver and receipt established;
Force(D) >>= typed rebind >>= body >>= designated result consumer
```

Every request from `D` keeps its origin, operation instance, live state and
shared `K,D`; bind appends the same suffix. If `d` bounds argument execution
and `b` uniformly bounds the body at every reachable post-force state under
the same assignment, `supp(D) ∪ ⋃ supp(B(v,C₁))` is a conditional upper bound
for this unfiltered support. It is not exact row addition and does not yet
interpret `[b,d]`. Retained entry, shallow handling, raw-continuation
re-emission, designated operation-result consumption, returned latent values,
and future callback invocations remain in the complete relation.

The intended pure-to-handler interface check still requires a derivation of
both clauses at shared `ν`:

```text
D_checked(ν) ⊆ D_actual(ν)
∀h ∈ D_checked(ν). P_actual(h) ⊆ P_checked(h)
```

The role-specific construction must supply the challenges, complete
observations, original profiles, typed `Flow`/receipt correspondences, and
event-specific `Observe`/incidence that make these clauses meaningful.
Handler role by itself grants neither capture authority nor new operation
arms. The displayed `never` remains uninterpreted as an effect port until that
source construction is derived; it cannot be equated with an empty row or
polarized solver extreme.

The compiler-referee review reported a BLOCKING closure finding against the
candidate complete-invocation theorem (the required challenge-domain
construction is absent) and major findings for decorated-behavior preservation,
the independent parameter-entry axis, and the insufficiency of support union
for full Function comparison. The specification audit found the role-first
direction conformant and confirmed those are open proof obligations, not a
conflict with the user's selected rules. This section records the exact
conditions; the findings remain open because no source-domain construction or
preservation proof has been produced.

The compiler-referee review found no evidence that `Rel_C`, shared `ν`, `K,D`,
`Flow`, `Observe`, incidence or existing subtraction cannot represent a
required fact. The blocker is missing source derivation/domain construction,
not a demonstrated carrier insufficiency. Keep implementation authority
closed. First derive the bounded source-elaboration clauses for the three
literal cases, using the callback fixture as the expected-context anchor.
Then derive the role-specific operational contribution behind `[b,d]` without
claiming full complete-domain comparison. The independent parameter-entry and
decorated-behavior obligations, `EnvStore`/`JointWF` construction, and
context-transition closure remain prerequisites for the later complete
inequality proof.

### Follow-up audit: contextual domains are not yet constructed

The candidate all-well-typed-context `CallCfg` in the coupled-interface draft
and the `D_i` notation in typed-core §9 give the right semantic shape but do
not close the BLOCKING gap. The coupled draft explicitly leaves its context
typing, environment relation, and typing/evaluation closure open. The typed
core comparison assumes admissible domains; it does not generate them from
source introductions. The two typed holes avoid requiring the tested callable
to be in its own denotation, but do not define the well-formedness of the
context's other environment/store, including recursive aliases and shared
lineage.

The existing value-hole non-vacuity argument also does not directly cover
Yulang's selected call rule. A callable and an already evaluated argument
value are not the same challenge as a callable plus an inert carrier of the
whole argument computation. For example, with a value-entry receiver
`f x = ()`, a carrier `D` that diverges purely before returning `Unit` never
reaches the body, while `Delay(Return Unit)` does; both have the same result
endpoint and empty effect support. Receipt must still be reached before the
force, so divergence cannot erase the carrier challenge from the call domain.
A retained receiver may ignore `D` and return; the receiver role alone does
not choose between these executions. This distinguishes the needed source
context rule without defining an effect meaning for `never` or invalidating
the existing coupled relation.

The missing proof input is a decorated source evaluation-context judgment
with callable and argument-code/carrier holes, an independently well-formed
environment and shared store at the same `ν`, and the source-owned lineage,
profiles, `K,D`, future inputs, responses, and raw resumptions. Context
admissibility must follow that judgment and source execution, not observed
calls, support filtering, arbitrary machine configurations, or success of the
comparison being defined. This is a proof premise/construction, not a proposed
solver carrier.

The later full-comparison theorem is **decorated source-context closure and
invocation coverage**. For every user-selected literal case, derive role,
actual §21 entry, boundary occurrences, and lexical evidence. Prove that each
jointly admissible function/carrier pair has a source application context
that reaches receiver receipt before argument force; prove source context
composition and execution preserve role/entry, stores, profiles, and the
shared fiber; and close future latent use and resumption under existing
`Flow`, `Observe`, incidence and expiry rules. For an existing value check,
construct actual and checked domains before comparison and retain the value's
actual entry and decorations. Then attempt the two §9 inclusions. A genuinely
empty argument fiber cannot establish annotation acceptance. The bounded
literal-role and callback-invocation derivation precedes this domain theorem
and does not claim to prove the complete comparison.

This first theorem may establish an extensional, potentially infinite semantic
domain. It does not also prove an effective finite presentation, principal
comparison, or a new source acceptance policy. No new carrier is justified;
the missing facts are source context typing and its closure theorem.

### Rigid-hole proof schema and remaining alias obligation

A second bounded Sol derivation gives a sound conditional proof schema, not a
domain construction. Write a target-typed context with proof holes:

```text
Γ; Σ ⊢ C : (□f:T_checked, □a:I_argument) ⇒ I_result
```

The holes are typed by the checked callable and argument interfaces but are
not inserted into `Γ`'s semantic environment. Separately assume a
source-admissible environment/store, an actual callable under its actual
interface, an argument code/carrier under its source interface, and their
joint `ν,K,D`/lineage consistency. Plug `f` and the inert argument carrier only
for execution. Do not invoke type preservation for the plugged program at
`T_checked`: that is the membership proposition under test. If
`D_checked ⊆ D_actual` is established, actual source behavior can be used for
those challenges, followed by the independent observation inclusion.

This still has one BLOCKING hole: removing `f` from the named environment does
not by itself define which source values or state reachable from `f`'s capture
are admissible in the context. A generic schema is a captured cell `ℓ` whose
value is `f` or a callback capturing `f`, with another context variable
aliasing `ℓ`; this is not yet established as a Yulang source execution.
Requiring that entire source state to satisfy checked membership reintroduces
the comparison being proved; excluding legitimate source aliases would narrow
the domain. `EnvStore` / `JointWF` therefore need a well-founded or guarded
construction over source-defined values, references, state transitions and
continuations, preserving the identities the source semantics actually
provides. Do not assume a primitive shared heap cell. No existing source
clause currently provides that construction.

The conditional immediate-application lemma is narrower and sound: if the
rigid-hole context and joint source-state premises hold for a runtime callable
and argument code, evaluation obtains the callee, inertly builds `Delay(D)`,
enters the callable's actual receiver, and establishes its receipt before
forcing `D`. Hence even a purely diverging `D` yields a nonempty invocation
challenge. This proves neither that every endpoint pair has a nonempty joint
fiber nor that the target challenge is in the actual domain.

The compiler-referee delta review accepted the rigid-hole/non-vacuity schema
conditionally and found no error in delaying actual preservation until domain
inclusion. It retained the BLOCKING context/environment/store construction
finding and a major context-transition closure finding: storing/copying the
closure, calling through aliases, handler exit, mutation, and raw resumption
must preserve role/entry, profiles, `Flow`/`Observe`, incidence and expiry in
one shared fiber. These are source-judgment/closure obligations, not evidence
for another carrier. Do not call §8's invocation-coverage theorem closed.

### Conditional open-graph route for the remaining EnvStore gap

A bounded Astra theorem audit, followed by a Sol architect delta audit,
identified a candidate proof route using existing graph identity and interface
evidence. It is a research candidate only; it does not discharge the
BLOCKING `EnvStore`/`JointWF` construction or transition-closure findings.

Use one proof-only rigid hole `H:T_checked` in open source derivations for the
context, containing closures, and saved suffixes. The hypothetical typing
assumption for `H` must never imply semantic membership of the actual callable
at `T_checked`. Build one joint source-identity graph for context roots,
captures, argument carriers and continuations; include shared locations only
where a source operation gives them that identity. Any cyclic structural
admissibility relation must be a displayed monotone positive operator over
source descriptors and existing decorations; the hole clause checks only the
designated hypothetical hole. Every containing closure remains justified by
its open derivation rather than by closed target membership. Plugging is
source-preserving substitution over the same identity graph, not a fresh or
independently selected state.

This structural relation alone does not establish a semantically valid
`EnvStore`. The new obligation is an open decorated source-typing and history
construction, with substitution and transition closure for each finite
source step. In particular, open dependence must be transported through
source-defined reference/state operations, alias calls, closure capture,
returns, requests and responses, handler exit, and raw resumption; it cannot
be approximated by a static “contains `H`” tag. Behavior after plugging
retains the actual receiver role and §21 entry, original profiles, shared
`ν,K,D`, event-specific `Flow`/`Observe`/incidence, and activation expiry. A
naive semantic greatest fixed point is not justified because Function inputs
are negative and mutable cells couple reads with writes.

The candidate's initial-state domain must not silently shrink to heaps
reachable from closed programs. The coupled contextual contract permits
semantic free-variable environments; whether open derivations with admissible
imports recover that domain remains unproved. Finite identity-preserving graph
machinery transports supplied relations but proves neither source generation
nor finite effective comparison or principality. Thus this route adds proof
judgments and closure lemmas, not a solver carrier, runtime provenance, or a
contextual-preorder interpretation of concrete inequality.

#### Step-indexed open-world candidate and proof gates

A compiler-referee audit of the proof-only route found step indexing to be a
plausible guard for recursive aliases, consistent with the already-recorded
logical-relation option in the coupled-interface draft. This remains a
candidate, not a defined relation. Its minimum shape is a family of bounded
approximants over one fixed actual callable, assignment `ν`, source
environment, and identity-preserving heap graph. The hole assumption is
available only at a strictly smaller index after a concrete source-machine
transition. At each index, quantify over all admissible lower-index caller
configurations, arguments, responses, and resumptions, preserving the actual
receiver entry and decorations. Full extensional validity would require all
finite indices; index exhaustion is never evidence of membership.

The same source state must be fixed across the approximants: `∀n.∃state_n` is
insufficient because independent witnesses can hide an inconsistent alias
state. The context domain must be exact: closed-program reachability would
exclude some of the selected semantic free-variable environments, while an
unrestricted graph-shaped import domain could admit impossible states. Open
derivations for closures containing the hole do not alone solve this domain
problem. Distinguish ordinary imports, whose semantic validity is independent
of the query, from hole-dependent values, whose behavior invokes the bounded
query recursively.

The indexed transition proof must catch a callback that calls the tested
function through a shared cell `N` times and then emits a forbidden request:
some finite index must reach the request and reject. Resetting fuel at receipt,
accepting on exhaustion, or carrying checked membership as a premise would
break this property. The world must follow the live source configuration and
state through handler exit and raw resumption, while a saved handler grant
must not survive expiry. The closure theorem must retain `ν,K,D`, original
profiles, typed `Flow`/`Observe`, incidence, and current activation identity.

Finally, finite-prefix adequacy must cover the whole complete-interface
contract, including challenge-domain admission, typed receipt, observations,
returned latent interfaces, later calls, and raw resumptions. A support-row
projection alone is insufficient. Prove that each failed domain or
observation inclusion has a finite witness in the indexed relation before
using the all-indices characterization. These premises remain open; the
audit found no solver-carrier insufficiency and establishes neither a finite
principal presentation nor an implementation path. The later proof work is to
define exact indexed imports/worlds, prove domain preservation and guarded
substitution/transition laws, then prove complete-interface adequacy. Those
are prerequisites for the full joint `[b,d]` inequality. A bounded source
derivation of literal roles and its operational motivation can proceed first,
without treating support accounting as that full inequality proof.

#### Source-state realization boundary

A subsequent spec audit found that the generic heap wording above cannot be
read as a Yulang source transition rule. The authoritative Yulang3 architecture
§6.9 distinguishes compile-time `StateSlotId` from runtime address, cell,
activation, or multi-shot-branch identity; §8.3 states that `&a = value` is
implemented as a pure continuation restart, not primitive in-place heap
mutation. The frozen `RefSet` characterization routes updates through
`update_effect` and its source handler; it does not establish the shared-cell
machine witness as a typed source execution.

Accordingly, captured-cell and write-before-resume examples remain
abstract-machine schemas until each operation is realized through source
State/reference behavior. The source-state world for any indexed proof must be
derived from the selected source transition relation: lexical reference
transport, State-slot ownership where visible, effect-mediated update, active
handler identity, and raw continuation re-entry. It must not introduce
primitive heap allocation/write steps or identify `StateSlotId` with runtime
cell identity. Conversely, do not exclude first-class reference values from
the Function challenge domain: architecture §6.9 keeps general refs such as
`std::io::file::text` separate and does not decide their coverage. Their
operations need their own source bridge if admitted by the interface.

This source refinement leaves the existing EnvStore/context-domain blocker
open. For the later full-comparison gate, derive the exact state carried by
source contexts and imports, connect local State and general-reference
operations to that state, then formulate step-indexed closure over those
actual transitions. This follows the bounded role/interface derivation.

#### Split source realization without splitting the solver relation

A bounded Sol architect derivation gives the next proof schema. Keep one
complete `Rel_C` and split only the source-realization proof into two paths:

| Source path | Existing facts | Missing source derivation |
|---|---|---|
| Visible local StateSlot | `HirModule` owns `StateSlotId`; `ConstraintStore` owns slot/read/write occurrences; one payload component and `StateEffect` atom are shared; visible alias/capture/escape preserves declaration origin; lexical exit discharges a nonescaping local atom | Define source configuration at declaration, read and update; prove update's continuation restart with replacement data; derive capture/resumption behavior; distinguish runtime activations of one static slot |
| General first-class reference | A stable-core fixture constructs a `ref` with captured `get` and `update_effect` callbacks, then calls `update` and `get` | Derive callback invocation, update request/response and handler behavior; define opaque reference transport, alias/capture/escape and resumed access for admitted imports |

The contextual challenge schema remains proof-only: a role-directed checked
context with rigid callable/argument holes, query-independent semantic
imports, hole-dependent open values/captures, and one jointly admissible
source configuration/history under shared `ν,K,D` and source-owned
occurrence/activation evidence. It must reach the actual callable's receipt
before force. Receiver role and §21 entry remain independent; existing values
retain their actual role, entry, profiles and decorations.

`Rel_C`, source occurrence/incidence, `Flow`/`Observe`, and existing
activation/continuation evidence are candidate representation for these
facts. The split does not propose new solver/runtime carriers and does not
prove they suffice: each path still needs guarded substitution/transition
closure and finite-witness adequacy for domain admission, receipt, complete
observations, latent returns and future invocation. In particular, the
fixtures establish local updates, captured reference callbacks and ordinary
recursion; they do not establish shared-reference state across multi-shot
branches or recursive storage of the tested callable. Keep those as open
source cases. No `StateSlotId` may be treated as a runtime cell/activation
identity, and first-class references remain in the domain whenever admitted by
their interface.

#### Concrete callback-context anchor

The stable-core `ref_update_local_buffer_public` fixture gives a concrete
role-first source anchor. It constructs a reference record whose `get` and
`update_effect` closures capture `$buffer`, then calls:

```yulang
r.update (\old -> old + "!")
```

The public signature contract for `std.control.var.ref.update` gives the
callback parameter shape `('c -> ['b] 'c)`. Under the user's source rule, this
unannotated literal receives handler receiver role from that callback expected
context before its Function interface is elaborated. Its body is pure string
concatenation; that fact does not select pure receiver role. This is a direct
application of the approved contextual-role rule, not a new Function subtype
rule or an Oracle-derived generalization.

The same fixture's `update_effect` closes over the local State value and
performs `&buffer = ref_update::update $buffer`. The authoritative
StateSlot/continuation decisions identify the local slot and its effect
evidence; the general-ref contract exposes the callback path. This connects
the two source-realization lanes at one concrete API use. The underlying
`std.control.var` implementation is not present in this workspace, so this
fixture does not establish the complete handler transition, `Rel_C` challenge
domain, multi-shot behavior, or the `[b,d]` lifting proof. Those remain
separate obligations.

#### Immediate gate refinement after the role-first clarification

The first task is now a finite source-elaboration derivation, not construction
of the complete contextual challenge domain. State the source clauses for the
three introduction cases independently of effect-row component syntax:

1. an unannotated function literal introduced without a handler expected
   context selects the pure receiver role;
2. a function literal with an explicit Function annotation selects the
   annotation's handler boundary;
3. a function literal supplied in callback position inherits handler receiver
   role from that expected callback context.

For each case, derive the resulting Function interface and keep its receiver
role separate from its §21 parameter-entry role. Only then derive how its
effect ports describe the source invocation. In particular, the displayed
`Fun(a, never, b, c)` is an inequality example whose port interpretation is
still to be derived from those source clauses; `never` itself contributes no
effect-position rule. Do not first assign every component a receiver or
computation denotation.

The `ref_update_local_buffer_public` callback is the bounded contextual
anchor for case 3. Use it to derive expected-context propagation and the
callback's handler interface. Then use the actual call/elimination rules,
including `Force(D) >>= B` for value entry, to explain the pure-function to
handler-capable callback lift jointly: `d` accounts for the forced argument
computation and `b` for body behavior at reached post-force states, under the
same existing `Rel_C` fiber and `ν`. This is a source derivation target, not
yet a complete inequality proof or unconditional row-union law. The
`std.control.var` implementation is unavailable here, so the fixture grounds
the contextual literal, not the library's whole operational path.

Keep the larger `EnvStore`/`JointWF`, alias/store transition closure, and
finite-witness adequacy proof as later gates. They are still required before
claiming complete-domain Function comparison, but they need not block this
source-introduction derivation. At each step, reuse existing `Rel_C`, `K,D`,
occurrence/incidence, `Flow`/`Observe`, and directed-weight/subtraction
evidence. The reread recorded in the progress audit found substantial prior
art in the old ordered push/pop histories, family budgets, common-row split,
residual transport and invariant payload checks. “Reverse addition” names no
new machinery. First show which source fact the existing evidence already
represents; propose an added proof object only if a specific required fact is
shown to be absent.

#### Bounded literal-role derivation (2026-10-03)

The existing finite core supplies a derivation skeleton without supplying the
new receiver role. For an ordinary literal lambda with parameter interface
`P` and synthesized body interface `I_b`, core §6 gives
`Value(Fun(P, Result(I_b)))`. Charter §21 generates `P` before body synthesis:
ordinary parameters enter as `Value(A)`, while explicit outer computation
annotations enter as `Computation(E,A)`. The user's receiver-role decision
adds a separate source choice before interpreting the Function's effect
ports:

| Introduction/check site | Receiver role selected before port interpretation | Existing construction reused | Effect-port status |
|---|---|---|---|
| Unannotated lambda synthesized without handler expected context | Pure | §21 parameter generation; core §6 body and result synthesis | Derive from the pure introduction's complete invocation view |
| Lambda checked against an explicit Function annotation | Handler boundary | Original annotation occurrence, typed paths and body/result checking | Derive from that annotation-selected boundary |
| Lambda checked in callback position | Handler from expected callback context | Expected callback interface plus the literal's own §21 parameter role | Derive from the handler callback invocation view |
| Already-constructed function value checked at a handler interface | Not a new introduction; preserve its actual role | Existing value checking and `Rel_C` comparison evidence | Any boundary/entry-changing adaptation needs source justification |

The first three rows select the receiver role before using any effect-row
component. The fourth prevents expected-type checking from retroactively
changing an existing value's executable entry or decorated behavior. In every
row, receiver role and `Value`/`Computation` parameter entry remain independent
source decisions, not one inferred from the other's ports.

The role-selection part can be stated without yet inventing an interface or
solver carrier:

```text
select-role(lambda, no Function annotation, no expected callback boundary)
  = Pure
select-role(lambda, explicit Function annotation F_ann)
  = Handler(boundary from F_ann)
select-role(lambda, expected callback contract F_cb)
  = Handler(boundary from that callback slot)
```

After this selection, the source derivation must elaborate the body and
complete Function interface under that role and its original boundary
profile. Charter §21 independently supplies parameter entry. The existing
core's `Value(Fun(P, Result(I_b)))` is only the constructor/result skeleton;
it does not define the role-indexed effect ports and cannot replace this next
elaboration step.

For the concrete callback case, the contextual propagation path is:

```text
application source rule
  -> callee's declared callback-value slot
  -> check the literal argument against that expected Function interface
  -> select Handler(callback-slot boundary) before elaborating its body
  -> generate the literal's own parameter entry by §21
```

The stable-core `r.update (\old -> old + "!")` fixture has the source shape
for this role rule: `update` has a declared callback-value parameter, and
`old` has ordinary value entry. The user's rule selects Handler for a literal
in that callback position. However, core §6 only synthesizes the argument and
constrains its whole computation interface against the formal; it does not
derive that the formal is passed into lambda introduction before body
elaboration. The expected-context propagation route above is therefore a
conditional source schema, not a consequence proved by core §6. The missing
lemma is to derive this pre-body contextualization while retaining the
inert-argument/receipt order. Neither the schema nor fixture proves the
role-indexed ports or pure-value-to-handler inequality.

For a bounded derivation with a known callee, the missing contextualization
clause has this candidate shape. If the resolved callee exposes a declared
ordinary value parameter whose source interface is a Function contract
`F_cb`, and the corresponding application argument is a Function literal,
the source application/lambda elaborator passes `F_cb` as the literal's
expected callback context before elaborating its body. That context selects
the Handler role and supplies the original callback-slot boundary/profile;
the literal's own parameter entries are then generated by §21. The checker
records the resulting interface constraints as ordinary `A <: B` solver
tasks, not as a separate compatibility judgment. Runtime argument
construction, receipt and entry still follow core §6 and §21.

This clause is a proof target derived from the user's callback-context rule,
not a theorem already present in core §6. It is bounded to a known
Function-valued formal such as `ref.update`; unknown callee heads, retained
computation formals, annotation overlap, actual/checked domain inclusion,
role-indexed effect-port construction and the full callback `CallView` remain
outside the clause. Its success criterion is that the slot descriptor reaches
literal elaboration before body synthesis without moving any runtime force or
discarding the source profile.

One overlap remains explicit: a Function-annotated literal can also occur in
a callback position. Both inputs select handler role, but this source audit
does not establish whether the annotation boundary is checked against, nested
inside, or otherwise related to the expected callback-slot boundary. The
elaboration theorem must account for both original boundary descriptors and
show how their concrete interface check uses the single `A <: B` solver; do
not merge their profiles or infer a profile from the solved effect row.
Resolving their source path relationship is part of the Function
annotation/context elaboration theorem.

A no-new-carrier candidate for the overlap follows the established distinction
between introduction and checking: the annotated literal is introduced with
the handler role and boundary selected by `F_ann`; the callback slot then
checks that resulting Function value against `F_cb` through the same concrete
inequality solver. The actual boundary/profile remains attached to the
introduced value, and the expected slot remains a separate use-site view.
This fits the rule that checking an already-constructed value cannot rewrite
its role or executable entry. It is not yet a source theorem: the annotation
introduction/elimination clause must show that this is the source ordering,
and the callback `CallView` still needs its typed profile projection.

Current syntax authority cannot close that premise. `syntax-v0` specifies
`as Type` as a generic `TypeAnnotationTail` on an `OperatorChain` and
explicitly excludes type meaning and checking
(`syntax-reference/en/src/expressions/operator-chain.md` §1; its associated
Hir only preserves the generic annotation node). Thus the candidate ordering
comes from applying the user's Function-specific boundary clarification plus
the general annotation checking rule, but the latter is not currently a
source-authorized rule in this successor package. Do not present syntax
ownership as proof of annotation-checking order.

The stable-core callback gives one concrete instance of row three. Its public
signature is
`ref('a & 'b, 'c) -> ('c -> ['b] 'c) -> ['b, 'a] ()`, and the source calls
`r.update (\old -> old + "!")`. The literal is in the callback's expected
position, so it receives handler receiver role before body elaboration. Its
ordinary `old` parameter has value entry under §21: the argument arrives as an
inert whole-computation carrier, then is forced and rebound once before the
body. For this entry case the existing operational law has shape
`Force(D) >>= B`; argument requests and the body's reachable post-force
behavior therefore belong to one invocation under the same `Rel_C`/`ν` fiber.
This justifies joint consideration of argument and body contributions, but
proves only the existing conditional support bound. It does not establish
exact `[b,d]`, a subtraction step, or a general Function inequality. If §21
instead selects retained `Computation(E,A)` entry, this force step does not
apply unless an explicit body consumer forces the carrier.

This derivation leaves a sharper gap than a general component-to-interface
map: the source clauses assign roles and construct the literal's interface
skeleton, but no source clause yet shows how an already pure-role Function
value is checked or adapted at a handler-capable callback boundary while
preserving its actual behavior. That is the direct bridge needed for the
pure-to-handler inequality. The actual and checked complete challenge domains,
effect-port interpretation and local adaptation evidence must be derived
there. Until then, `Fun(a, never, b, c)` is notation in the intended comparison,
not a source clause assigning meaning to effect-position `never`.

No existing evidence gap has been shown. Continue with one concrete
source/application derivation and crosswalk its invocation occurrences to
existing `Rel_C`, `K,D`, occurrence/incidence, `Flow`/`Observe`, and applicable
directed-weight/subtraction witnesses. If that derivation identifies a
specific fact unavailable in those carriers, state the fact and its source
owner before considering additional evidence. This construction remains
proof-only and grants no implementation authority.

#### Callback-slot view for an existing pure-role value (conditional derivation)

The typed-boundary and coupled-interface drafts give a candidate source
route for the remaining pure-value-to-handler-callback bridge. Keep three
facts distinct:

1. the function literal's introduction selected its actual receiver role;
2. the callback slot's expected interface selects a handler-capable typed
   `CallView` for uses through that slot;
3. the actual callable's §21 entry still determines whether its received
   argument carrier is forced/rebound or retained.

Under this reading, checking a previously constructed pure-role function at a
handler-capable callback interface does not rewrite the closure's role or
entry. The typed callback-slot view encloses the ordinary call. For a
value-entry actual callable, the source schedule remains: evaluate the
callback/callee, inertly build the whole argument carrier, establish actual
receipt, then execute `Force(D) >>= B` inside that call. With identity value
and result transport, no pre-call conversion force and no synthetic receiver
are needed. The handler-capable slot's current `CallView` supplies the
observation port for requests from the forced argument and body; existing
`Flow`/`Observe`, occurrence/incidence and `K,D` retain their separate
ownership at the same `ν`.

If `d` bounds the argument execution and `b` bounds body execution at every
reachable post-force state under that same assignment, the complete
value-entry call has the conditional support upper bound `supp(d) ∪ supp(b)`.
This is a bound on one state-threaded call relation, not an equation obtained
by independently subtyping effect ports. Multi-shot resumes, handler image,
returned latent paths and future invocations remain in the complete relation;
no row contribution may be dropped merely because a first call returned.
Retained `Computation(E,A)` entry does not use this `Force(D)` argument unless
the source body explicitly consumes it.

This gives an operational source explanation for why a handler-capable
callback interface can need the combined argument/body effect view while
preserving an actual pure-role closure. It does not yet derive the complete
`Fun(a, never, b, c) <: Fun(a, d, [b,d], c)` inequality: the source elaboration
must still show that the callback expected context creates exactly this slot
view, that its observation profile denotes the target port, and that the
actual/checked complete challenge domains satisfy the joint containment law.
The identity-transport case also does not settle non-identity argument/result
adaptation; a generic pre-call FunctionMap cannot be assumed because it may
force before actual receipt.

The function-adapter equation in the typed-boundary draft is a conditional
realization of `Adapt(A_t,A_s) >>= Call(f) >>= Adapt(B_s,B_t)`, not authority
for moving `Force` before receipt. The callback-slot derivation reuses its
complete-CallView scope and the coupled relation's event observations, but
adds no new adapter, regional, attachment, or provenance carrier. The next
source proof is the callback-slot elaboration/receipt diagram and its identity
adaptation instance, followed by a witness that the effect-port projection
contains both contributions under one `Rel_C` fiber.

#### Existing evidence crosswalk for that proof

The typed-boundary draft already gives the relevant evidence vocabulary; the
candidate derivation need not duplicate it:

| Source fact | Existing evidence | Exact use in the callback proof |
|---|---|---|
| Expected callback contract belongs to receiver `r`, slot `a`, profile `Γ`, and endpoints | Callback-boundary identity `b=(r,a,Γ,endpoints)` | Source elaboration must construct this `b` at callback-slot introduction/use; do not infer `Γ` from a solved row |
| A received callback value is viewed at a particular signature position | Typed view `(v,t,e)` and `Receive(u,slot,view,typed correspondence)` | Preserve the actual value and its pure-role introduction while checking the slot view |
| Argument, result, and latent typed paths correspond across a view | `Flow` and path-indexed profile/dependency transport `χ,K,D` | Carry original typed-family dependencies through identity or admitted conversion |
| A request is exposed by the executing callback invocation | `Observe(q,v,p₀)` from the source computation relation | Locate both Force-exposed argument requests and body requests at the complete `CallView` ports |
| A request has typed route to a concrete handler contract | Existing `Path` then current-configuration `Inc_C` | Keep profile/path evidence separate from current receiver/handler activation and ordered search |
| Effects of argument conversion, call, result conversion, and demanded force | One complete source `CallView` | Preserve receipt order and include all demanded stages without a site-specific callback row rule |

For the identity-adaptation case, the source proof should show the callback
value reaches the slot view without executable argument/result conversion.
The actual invocation still forces the argument only at its §21 value-entry
point. The single `CallView` then exposes events from that force and from the
body. The target effect port may cover both only if its source-derived profile
and typed paths witness both `Observe` edges under shared `ν,K,D`; merely
seeing their family names in a flattened row is insufficient. This is the
precise port-projection lemma left to prove.

The candidate source rule is therefore small and testable: an expected
handler-capable callback slot supplies one source-decorated view; calls through
the slot retain the callee's actual entry and compose through the existing
complete `CallView`. It is not yet an adopted general checking rule for every
pre-existing function value. Its derivation must establish the callback
boundary profile, typed receipt, identity transport and both event paths from
source typing. The whole-source challenge-domain and finite-presentation
theorems remain later gates.

#### Immediate gate revised: receiver-role elaboration precedes slot projection

The current immediate gate is the source-level judgment that chooses receiver
role and elaborates a Function boundary. The intended ordering is:

```text
function introduction + expected context
  -> receiver role (pure / handler)
  -> Function interface elaboration
  -> effect-port interpretation
```

The three required cases are an ordinary unannotated function literal (pure),
an explicitly Function-annotated literal (its annotated boundary is a handler
boundary), and a callback-position literal (handler role selected by expected
context). Keep this receiver role independent of §21's syntax-directed
`Value`/`Computation` parameter entry. The source-computation-role package
records fixed-role skeleton inputs and original annotation slots, but does not
derive this role-selection judgment or its interface/effect-port clauses.
Thus the immediate missing source fact is the role-directed introduction and
contextual-elaboration rule, not a uniform map from one effect-row component
to a complete receiver/computation interface.

This user clarification supersedes the earlier charter §16 statement that
every function is a handler, specifically its universal receiver-role claim.
Its common invocation and argument-entry mechanics remain applicable under
the role selected here; §21 value entry still forces and rebinds within the
invocation for a pure-role function. The charter records this narrow
supersession in §24.

Effect ports acquire their interpretation only after that source elaboration;
they are views of the resulting Function interface, not independent
receiver-semantics inputs. In particular, the intended
`Fun(a, never, b, c) <: Fun(a, d, [b,d], c)` remains a later consequence to
derive from the pure-to-handler callback adaptation and its source call
semantics. No effect-position meaning is assigned to `never`.

The previously identified callback-slot profile projection is downstream of
this gate: once the handler-capable Function interface is source-derived,
derive its expected callback boundary, typed receipt and identity `Flow`, and
the separate `Observe` paths for `Force(D)` and body requests into the same
invocation port under one `Rel_C`/`ν` fiber. This reordering does not change
the existing evidence vocabulary (`Rel_C`, `K,D`, occurrence/incidence,
`Flow`/`Observe`, `Path`, `Inc_C`, and directed-weight/subtraction evidence)
and establishes no need for a new carrier. The already-constructed
pure-role-value comparison and complete actual/checked challenge inclusion
remain later obligations. This is a proof-only gate refinement, not
implementation authority.

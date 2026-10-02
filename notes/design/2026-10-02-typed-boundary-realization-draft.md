# Typed-boundary realization: scope choices and finite adapters

Date: 2026-10-02
Status: Draft; typed-value transport selected by user; conditional transport and adapter packages reviewed; full realization open; no implementation authority
Scope: completion of boundary relevance and structural Function/Thunk adapters
Approved-by: user for typed-value transport principle only (2026-10-02); exact realization and implementation unapproved
Drafted-by: primary with scoped-boundary and adapter-construction architect inputs
Reviewed-by: compiler_referee and spec_auditor for adapter and transport packages, 2026-10-02; fresh compiler_referee transport repair delta clean
Supersedes: none

## 1. Remaining definitions, not another effect mechanism

`2026-10-02-source-realization-and-symbolic-basis.md` isolates two source
definitions needed to instantiate the finite presentation: effective callback
relevance and effective general adaptation. This package advances both without
changing selected behavior. The user has selected typed-value transport for
both §2 scope choices; §6 supplies its common relation and proof candidate.
A finite structural adapter construction is proved in §§3–5.

The unchanged requirements are: an explicit concrete callback contract governs
both direct requests and caller-owned requests exposed by `Force` in its
complete `CallView`; hidden origin cannot veto that contract; receiver/handler
expiry ends authority; escaped values retain latent behavior and symbolic
`K,D`; raw shallow resumption uses current state outside the selected handler.
Oracle routing does not define any rule here.

The adapter result is a structural operational subtheorem, not a new supported
source envelope. It does not supply source typing, all conversions, arbitrary
unknown-shape instantiation, or the missing component interaction theorem.

## 2. Resolved source scope choices

On 2026-10-02 the user selected typed-value transport for both alternatives
below. Boundary/protection follows corresponding source-level typed value
paths through arguments, lexical environments, stores, returns and structural
adapters. Latent results retain it only along their corresponding signature
paths. Receiver/handler expiry disables the associated authority/protection;
origin, event identity, latent effects and symbolic `K,D` remain. This is a
semantic principle, not implementation approval. The comparisons below record
why this decision was needed; they are no longer unanswered questions.

A declared callback boundary can be represented by
`b=(receiver activation, callback slot, typed contract)` and a typed view of
the callback value. Entering that view covers argument adaptation, the call,
result adaptation and demanded forces. Nested computation preserves enclosing
view instances; requests record the applicable instances independently of
origin. Candidate testing filters them using the *current* active receiver
and handler occurrences. This realizes the selected cases for explicit
callback uses, but does not determine every value-transport case.

### Handler territory through a captured environment

Consider this semantic scenario, not an executed Oracle fixture:

```text
outer handler h0 handles E
receiver r receives caller callback f
r defines helper g capturing f in its lexical environment
g installs its own handler hg for E, then calls f
hg has no concrete capture contract for f
```

The source description distinguishes `r` and `g` activations. An enclosing
grant to a handler owned by `r` does not by itself grant authority to `hg`.
That does not yet determine whether `hg` has *ordinary* eligibility:

| Interpretation | Treatment of `hg` |
|---|---|
| Only declared argument boundaries determine territory | No `g` callback argument boundary is crossed; `hg` may handle ordinarily |
| Callback value transport preserves protection across environment/store paths while the receiver is active | Capturing `f` does not remove its receiving-side protection; `hg` needs an applicable local concrete contract and otherwise forwards |

The second is the selected direction for avoiding capture merely by changing
an argument into a lexical capture. It requires one general typed-value
transport/handler-territory rule. Wrapping every callable environment value
would be unjustified: ordinary local closures and direct operation values
must not become protected callback inputs merely because they are callable.
Nor may an enclosing grant be copied into a new helper grant by family equality.

### Latent values after the complete CallView returns

Suppose a callback returns an unexecuted thunk or closure, and the receiver
executes that returned value after the callback's complete `CallView` has
returned but before the receiver activation ends. This differs from the
already-selected case of a force *inside* result adaptation.

| Interpretation | Later latent execution while receiver remains active |
|---|---|
| Execution-view scope | The completed callback view adds no boundary at this later entry; current ordinary boundaries determine eligibility |
| Typed-value scope | The returned value retains the typed boundary reference; later entry consults that contract while its receiver is still active |

Both retain latent effects and `K,D`, and both remove the old receiver's
authority/mask after its activation ends. They can differ before expiry; for
example, an absent/wildcard contract does not authorize a receiver handler
under the second interpretation, whereas the first can permit ordinary
handling outside the former view. The exact effect depth/typed result path
to which a contract applies must be part of the common value-boundary rule;
this comparison does not authorize copying one effect annotation onto every
nested latent result.

These were source-choice discriminators, not complete alternative calculi
with established soundness/principality. The reply selects transport through
both paths with activation-scoped lifetime. It does not authorize copying an
outer annotation onto unrelated nested effect ports. The choice is resolved;
the exact common realization and its source applicability require the proof
below. The structural adapter subtheorem does not depend on choosing its
concrete runtime representation.

## 3. A finite structural adapter kernel

### Fixed-shape graph and explicit equivalence candidate

Let `T` be a finite rooted graph of constructor nodes:

```text
Atom(a)                 a ∈ {Unit, Bool, Int}
Fun(argument, result)
Thunk(effectLabel, result)
```

Every reference targets another node. Recursive edges refer directly to
constructor nodes; there are no constructor-free alias cycles. The three
atoms are rigid tags, not variables whose assignment can change them into a
function or thunk. The finite effect labels retain their symbolic family
endpoints and constraints; ground effect arguments need not be finite.

For this operational kernel define `≈g` as graph bisimilarity respecting
constructor/atom tags and exact symbolic effect-label identity. Start with
all pairs and repeatedly delete pairs whose tags/labels disagree or whose
required child pair is absent. At most `|T|²` pairs are deleted, so this is
effective even for recursive graphs. The final relation is a bisimulation;
every bisimulation is retained by induction over deletions, hence it is the
greatest one. No type solver or concrete materialization is hidden here.

This is an explicit *candidate* for the structural subtheorem, not a selection
of the successor's general boundary equivalence `≈`. Distinct symbolic effect
labels can denote equal effects under some `ν`; `≈g` need not identify them.
The theorem interprets the displayed source equations using `≈g`. A bridge
to a different selected equivalence requires its own preservation argument.

### Pair graph construction

For an ordered source/target pair `(s,t)`, insert a placeholder in a memo table
*before* following children. Fill it according to this priority table:

| Condition | Descriptor | Child pairs |
|---|---|---|
| `s ≈g t` | `Id` | none |
| `s=Thunk(E,a)`, `t` not Thunk | `ForceThen(d)` | `(a,t)` |
| `s` not Thunk, `t=Thunk(F,b)` | `DelayThen(d)` | `(s,b)` |
| `s=Thunk(E,a)`, `t=Thunk(F,b)` | `ThunkMap(d)` | `(a,b)` |
| `s=Fun(a,b)`, `t=Fun(c,d)` | `FunctionMap(darg,dres)` | `(c,a)`, `(b,d)` |
| otherwise | uncovered pair | none |

After the identity case the three thunk cases are disjoint. Each pair is
processed once; back edges reuse its placeholder. For any finite set of roots,
at most `|T|²` descriptors with at most two child references each are needed.
No recursive source type or adapter is expanded into a tree.

An uncovered reachable pair means this kernel supplies no operational
realization for that root. It is not a successor `ill-typed` diagnostic,
does not establish absence of another source conversion, and does not publish
a partially realized root. The graph is a research construction, not a
compiler API or resource-limit decision.

## 4. Operational interpretation and proof

Use the existing state-threaded `Return`, bind, `Force`, source `Delay` and
source `Call` operations. `RunD(d,v,C)` denotes descriptor execution with
current source configuration `C`:

```text
Id(v)                = Return(v)
ForceThen(d)(v)       = Force(v) >>= (λx. RunD(d,x))
DelayThen(d)(v)       = Return(Delay(RunD(d,v)))
ThunkMap(d)(v)        = Return(Delay(Force(v) >>= (λx. RunD(d,x))))
FunctionMap(da,dr)(f) = Return(FunctionView(f,da,dr))

Apply(FunctionView(f,da,dr),x) =
  RunD(da,x) >>= (λy. Call(f,y) >>= (λz. RunD(dr,z)))
```

Omitted `C` arguments are threaded by bind exactly as in the adequacy package.
`Delay` and `FunctionView` store the input value and child descriptor IDs;
they do not execute child conversions at construction. They retain source
lexical references and whatever boundary lineage the ultimately selected
source value-transport rule requires. They do not capture mutable-store
contents. Function application/resumption later uses the actual current store.

The view is an administrative realization of the complete source `CallView`;
it does not install a fresh receiver/handler or manufacture capture authority.
`Id` eliminates only value-conversion work. The surrounding typed-boundary
entry/exit and explicit annotation contract are still executed by the source
rule, even when source and target value shapes coincide. The type graph does
not identify an omitted annotation with an explicit capture contract merely
because their inferred effect labels agree.
If source boundary semantics surrounds that view with a scope, the same scope
surrounds argument conversion, underlying call, result conversion and all
demanded forces on both sides. This policy is a shared parameter, not a
hidden implementation of the §2 decision. The theorem below assumes
the same source `Delay`/value-lineage behavior on both sides and does not
certify its still-pending finite realization.

**Theorem (finite operational realization).** For every covered root pair
and input value/configuration of the corresponding source shape, descriptor
execution simulates the structural source adaptation equations with `≈g`,
preserving returns, request prefixes, latent future calls/forces, current
state and raw resumption behavior. It emits the same requests as those
equations; it performs no row subtraction.

Proof: relate every reachable `(s,t)` source adaptation command to its memoized
descriptor, and relate suspended binds by their corresponding suffix stacks.
Unfolding one command chooses the same priority-table case. `Id` returns the
same value. `ForceThen` invokes the same source force and appends related
child conversions. `DelayThen` and `ThunkMap` return related latent values;
on each future force they execute the same source operations before entering
the related child. `FunctionMap` returns related views; every application
uses the contravariant argument pair, the same underlying call and the
covariant result pair. The stateful bind lifting lemma composes these matches,
including every typed admissible resumption. All symbolic endpoint references,
request origins and still-live `K,D` are transported by those same source
operations under one `ν`.

For recursive pairs the relation contains all memoized pairs at once.
Descriptor recursion either returns a latent value/view or executes an actual
source force before its child; function children are entered only upon source
application. There is no descriptor-only cycle that repeatedly expands type
aliases. More explicitly, matching command configurations count each source
force/call entry and each adaptation-clause unfolding as a step; each
descriptor clause has the same corresponding operational step. Thus an
infinite chain of forced computations is matched by an infinite source
execution, not declared convergent by memoization. Induction covers finite
prefixes, and the simultaneous command relation covers unbounded execution.
The argument never requires recursive syntax to be unfolded in advance.

This is an operational simulation, not a proof that a proposed conversion
satisfies its target type/effect contract. In particular the delayed target
must cover the whole source force plus result adaptation. The complete
interface/certificate must validate that condition using the common source
relation; neither a `ThunkMap` tag nor equal family heads proves it.

## 5. Consequences and remaining source bridge

### Symbolic label-equality extension

For fixed constructor graphs one can also construct a symbolic structural
equivalence candidate without materializing family arguments. Add the finite
set of label-equality predicates for encountered thunk-label pairs to `PΩ`.
Represent formulas by truth tables in the finite Boolean algebra of the
finite-presentation package, rather than raw syntactic expression trees.
For pairs `s,t`, define the operator in that algebra:

```text
F(X)_s,t = false                                  mismatched constructors/atoms
         = true                                   identical rigid atoms
         = X_arg(s),arg(t) ∧ X_res(s),res(t)       two Function nodes
         = LabelEq_s,t ∧ X_res(s),res(t)           two Thunk nodes
Eq = νX. F(X)
```

Here `νX` denotes greatest fixed point, not the type assignment `ν`. Iterate
from all true formulas. At each Boolean valuation at most `|T|²` pair entries
can be removed; therefore the vector stabilizes after at most `|T|²` rounds.
Evaluation under any realizing assignment commutes with each iteration, so
the result is exactly greatest structural bisimilarity with that assignment's
label equality. Unrealisable Boolean cells assert nothing about a source
assignment.

Replace each descriptor's identity-first decision by a finite guard
`if Eq_s,t then Id else structural-case`. Allocate the descriptor before its
children as before; each pair still has bounded descriptor size. This gives
a symbolic generator and the same operational simulation if the source
selects this structural meaning for `≈`. Guard evaluation/realizability still
needs the underlying type theory. Neither version is selected here as the
general source equivalence. Equal labels do not identify callback boundary
ownership, event identities, annotation forms, or `K,D` endpoints.

### Source bridge

The graph construction gives a concrete finite family of adapter code labels
and bounded wrapper records for the earlier `Ω` machine: a child descriptor
is a graph pointer, not an unbounded host function. Finite symbolic endpoint
queries remain attached to the original pairs. Allocation of another runtime
wrapper creates no new type endpoint. This discharges the operational
adapter-descriptor premise for this fixed-shape kernel, conditional only on
the already explicit source primitives/value-lineage policy.

It does not discharge these broader obligations:

- deriving finite resolved shapes, admitted conversions and force positions
  from source inference; an unknown type endpoint whose `ν` may be a thunk
  cannot be treated as a rigid atom to obtain this theorem;
- proving that general source `≈`, other data/value conversions, and all
  recursive typing cases agree with or extend this kernel;
- realizing the selected §2 source territory/latent transport rules and proving their
  finite realization, including invocation re-entry;
- a uniform modular future-interaction presentation and the source
  typing/acceptance bridge, then lifecycle and implementation gates.

No source envelope is narrowed and no acceptance difference is approved.
This constructive finite recursive adapter graph is a component of the
Milestone-3 route, not a complete finite successor or a class-3 result.

For the first gap, `(α,Unit)` is a concrete obstruction to *this fixed-shape
construction*: assigning `α=Unit`, `α=Thunk(E,Unit)`, and an arbitrarily deep
nest of such thunks demands identity, one force, and repeated forces. The
endpoint name remaining `α` does not make its outer constructor fixed.
Pair memoization over the given source nodes alone does not supply those
different payload nodes. This does not prove impossibility of a finite
parametric descriptor interpreter or richer symbolic presentation, and does
not justify rejecting such source uses. Its resolution belongs to the
source elaboration/representation bridge.

## 6. Common typed-view transport

### Views, signature positions and introductions

Fix the finite monomorphic ownership/signature descriptors of the source
realization package and one assignment `ν`. A typed value occurrence is a
view `(v,t,e)`: underlying value identity `v`, signature position `t`, and
evidence root `e`. Evidence is attached to a *view*, not to the underlying
closure, cell address, type variable or effect-family head. Two aliases of
the same value need not have identical boundary views.

A signature has effect-observation positions, with structural paths to them.
The paths distinguish function computation/result, thunk computation/result,
and structural components. They are not identified merely because they end
at equal type variables or the same family. Recursive signatures retain a
decorated graph with explicit annotation occurrences; sharing the undecorated
type graph does not erase those occurrences or their depth.

At a source callback boundary, introduce a fresh boundary instance

```text
b = (receiver r, callback slot a, signature profile Γ, type endpoints)
```

`Γ` marks exactly which computation positions of that received typed value
are protected, and which have a concrete capture contract. An omitted or
wildcard capture annotation supplies protection at the applicable callback
positions but no concrete grant. Positions not exposed/protected by the
signature receive no incidence. The profile is part of the source contract,
not reconstructed from inferred row support. An outer effect annotation is
not a label on every descendant position.

This introduction is distinct from transport: copying a view never allocates
a new boundary or upgrades protection to capture. Signature profiles are
supplied by source elaboration; deriving all profiles from arbitrary syntax
remains the earlier elaboration gate.

### One relational transport operation

Let `χ_e(p,b)` record the persistent boundary profile of a view at typed
effect position `p`; it stores source profiles and ownership references,
never a cached fact that a handler was admitted. A typed value-flow derivation
supplies correspondences `M_i(p,p′)` from disjoint source view/port indices
`i` to target positions. Define the general multi-input relational image,
retaining each source witness and its provenance:

```text
χ_out = ⋃_i M_i* χ_i
(M_i* χ_i)(p′,b) iff ∃p. χ_i(p,b) ∧ M_i(p,p′).
```

The unary `M_*χ` is the one-source case. A fresh result view retains both the
actual returned value's evidence through its value correspondence and the
projected callee-result profile through matching typed result paths. These
are sources of the same operation used for other typed value flow, not a
separate rule for returns. Underlying pointer equality never unions all alias
views.

The correspondence is generated by ordinary typed structure. Binding a view
without changing its type uses identity. A structural projection removes
exactly its selected component prefix. Returning a function's result or
forcing a thunk removes its result prefix for the returned value; an emitted
request instead observes that computation's effect position. Structural
adapters use the argument/call/result correspondences of their descriptor,
with argument direction reversed where the function conversion is
contravariant. No correspondence is generated by family equality.

For example, if a callback's value signature has distinct positions
`call.effect` and `result.latent.effect`, result transport maps the latter
to `latent.effect` of the returned view. It does not map `call.effect` there.
Hence the former annotation cannot become a grant on a returned nested thunk
unless the signature independently puts applicable boundary information at
the corresponding result position. If protected `f` is returned through `g`
and `g`'s result profile contributes no protection, the actual-value source
still retains `f`'s profile. Conversely, a plain actual result can acquire an
independently annotated callee-result profile only at its corresponding typed
result paths; a root outer annotation cannot be copied across all result
ports.

Argument binding, capture into a lexical environment, storing/reading a
typed value, returning it and structural adaptation all execute this *same*
operation with their typed correspondence. A heap write stores the resulting
view, not just `v`; reading composes that stored view with the read position's
correspondence. This is one invariant on typed value edges, not separate
argument/environment/store/return hygiene rules. Private fields of a closure
are not exposed by transporting its public view.

### Receiving ownership and observation

To define handler territory, extend the value-flow graph with a receipt

```text
Receive(u, slot, view, typed correspondence)
```

when invocation `u` obtains that view in one of its typed bindings. Bindings
include parameters, its captured lexical bindings and values obtained during
execution. This receipt records ownership of the *use*; it creates no
boundary or concrete contract. A handler's owner is the invocation installing
it. Merely using a value as the callee does not make that callee's own
invocation a recipient of its callee view. The closure body starts from its
original captured bindings and actual arguments, each with their own views;
the callee's public view is not pasted onto all of its private bindings.

Request observation composes the generating/inherited computation path with
the complete currently executing typed `CallView`. All requests exposed in
that view, including requests from forced caller-owned thunks, use its typed
observation positions. The request's original origin, fresh event identity,
and symbolic `K,D` are carried independently. Outside that view, another
request cannot use its contract merely because its family matches. A later
latent observation opens the transported result view and uses its own
remaining signature positions.

The evidence graph has only introduction, typed-flow, receipt and observation
edges. `Path(q,u,b,p)` is its raw least path relation: from event `q`'s actual
observation, follow matching typed correspondences to a protected position
`p` of boundary `b` and a receipt by `u`. Intermediate ports must match; a
route from another alias or unrelated event is not a witness. Ambient
CallView observation adds the corresponding event path, not all boundary
histories attached anywhere to an underlying value.

Persistent profiles and paths are distinct from candidate-specific incidence.
For current candidate handler `h` owned by `u = owner(h)`, define at its actual
search configuration `C`:

```text
Inc_C(q,h,b,p) iff
  Path(q,owner(h),b,p) ∧ Active(h,C) ∧ Active(owner(h),C)
  ∧ Active(b.receiver,C)

Protected(q,h,C) iff ∃b,p. Inc_C(q,h,b,p)

Grant(q,h,C) iff
  ∃b,p. Inc_C(q,h,b,p) ∧ b.receiver = owner(h)
        ∧ Γ_b explicitly admits q.operation at p under ν

Visible(q,h,C) iff
  Active(h,C) ∧ Active(owner(h),C) ∧ Covers(h,q.operation)
  ∧ (¬Protected(q,h,C) ∨ Grant(q,h,C))
```

Expiry of this exact handler occurrence makes all of its `Inc_C`, `Protected`
and `Grant` facts false even while its receiver remains live. Receiver expiry
clears every candidate incidence rooted at that receiver. Raw profiles may
remain in views; neither raw `Path` nor `χ` itself is a grant.

The grant discharges transported callback protection for this event and this
receiver. This follows the selected preservation/no-origin-veto principle:
an older protected view cannot veto a concrete contract under which the
request is currently exposed. An enclosing receiver's grant is not local to
a nested owner and cannot authorize its handler. No independently motivated
invalidating boundary is specified in this ordinary calculus; introducing
one later requires its own source justification and a delta proof. Static
result filters and `OpCompat` remain typing constraints, not new dynamic
vetoes. Handler order, pattern/guard evaluation and actual selection are
unchanged; `OpCompat` checks the selected arm afterward.

### Transport and lifetime theorem package

**Composition.** For any two typed correspondences `M,N`,

```text
N_*(M_*χ) = (N ∘ M)_*χ,       Id_*χ = χ.
```

Expand membership on the left: there are intermediate positions `p,p′`
with `χ(p,b)`, `M(p,p′)` and `N(p′,p″)`. Those are exactly the witnesses for
the right side. Identity is immediate. Relational image also distributes over
source union: `N_*(⋃_i M_i*χ_i) = ⋃_i (N ∘ M_i)_*χ_i`. The same indexed
source witnesses establish this law without merging alias provenance. Thus
changing an argument route into an environment/store route with the same
typed composite correspondence and receiving ownership does not change
applicable boundary information.
The theorem does not equate programs that introduce different source
contracts or cross different receiver activations.

**No authority creation and depth preservation.** Every output profile has
an input boundary witness at a corresponding signature position. Induction
over the same equation therefore rules out new boundary IDs, grants from
wildcards, and a root annotation appearing on an unrelated nested port.
Receipts create ownership edges only. `Grant` additionally requires the
original receiver identity and its explicit local annotation. Equal families
or equal underlying value pointers cannot supply these witnesses.

**Current-scope filtering.** For a fixed candidate `h`, let `live_C^h χ`
retain a profile witness exactly when `h`, `owner(h)` and its original
`b.receiver` are active in `C`. Transport preserves these references, so
`M_*(live_C^h χ) = live_C^h(M_*χ)`, also for the multi-input image. The same
candidate, current configuration and original source identities are tested
on both sides of each existential witness. This law does not claim that
activity remains constant across execution. Expiry of `h` removes all its
candidate incidence, protection and grants; expiry of a receiver removes all
incidence rooted there. Neither removes latent effects or type predicates.
Persistent source profiles can remain when a receiver is live, but a different
handler `h′` must derive fresh incidence from an actual current path, its own
owner and its applicable local contract. Family equality cannot reuse `h`'s
incidence or infer authority for a nested helper.

**Receiving-side consequence.** A helper binding a protected callback through
its environment/store receives the same boundary view that argument
transport would carry. Its event path therefore reaches its own receipt.
Without a local explicit grant, its handler forwards. An outer grant belongs
to another owner and cannot change this result. In contrast, a handler in the
original callback body does not receive the callback's callee view merely by
executing its body. It handles its own ordinary body requests unless its own
received inputs independently impose protection. This is the consequence of
callee observation versus typed binding, not a helper-specific exception.

**Complete observation.** A direct request and one exposed by `Force` during
the same concrete callback view share its boundary/receipt observation path.
Both derive the same receiver-local `Grant`. Any extra inherited protection
on the forced thunk cannot veto that grant; its origin and `K,D` remain
distinct. Ordinary nesting extends the event path without removing a still-
active local grant. A request outside that view has no such observation
witness. For a returned latent value, future observations use the projected
result profile, giving the same argument after the original CallView has
returned. Receiver expiry instead invokes current-scope filtering.

**Symbolic incidence.** Boundary profiles, typed-flow maps, value and request
views and predicates use the same symbolic endpoints and `ν`. Attach each
live `K` predicate and its `D` links to the same transported view graph.
Composition joins these records; it neither solves them independently nor
discharges them when callback protection expires. A request disappearing from
immediate support is not a proof that its family predicate has no remaining
dependent view. This establishes preservation by the transport operation;
solver substitution and scheme lifecycle remain their separate gate.

### Concrete realization and proof boundary

For a finite execution prefix, bounded records store boundary profiles,
typed-flow edges, receipts, observations and view roots. Structural paths are
advanced one declared edge at a time. A repeated recursive signature node
does not identify different view/evidence occurrences. A query traverses the
finite evidence graph in product with the supplied finite profile/map states
and candidate owner, with a visited set. It checks activity of the exact
handler, its owner and the original receiver by the current activation roots
and uses the finite symbolic `Admit` predicates.
This computes the raw least path relation and its current candidate incidence
filter above without a hidden `Visible` oracle. Introductions, composition and
receipts create exactly their rule witnesses; induction on those rules proves
the stored graph and declarative relation agree. Finite-address abstraction
must retain every concrete route and uncertain identity outcome, rather than
treating a collision as equality.

Raw continuations retain views and use the resumed live store and active
roots. They do not make all reachable receiver/handler records active.
In shallow selection, consumed handler `h0` is gone: all of its incidence,
protection and grants are false. Resuming raw `k` preserves source views but
does not restore `h0` or its old grant. A later `h′` obtains only incidence
derived from its actual current path and local ownership/contract.
Source-prescribed invocation re-entry must provide its actual current owner
references; transport itself neither revives an ended activation nor invents
a contract for a fresh one. The precise re-entry owner mapping remains a
source-realization premise, especially for repeated resumptions; the above
lifetime theorem is conditional on that invariant, not a proof of it.

The new relation closes the common transport algebra and supplies a candidate
effective territory query for finite signature descriptors. Full source
realization still must derive the profiles, correspondences and re-entry
ownership from every source rule, cover unknown shapes and open clients, and
establish the source typing/acceptance bridge. The generic principal-certificate
theorem then applies to a sound realized graph; this section alone proves
neither full source safety nor principality of the successor. No compiler
implementation follows from the user's semantic choice.

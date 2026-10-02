# Source-to-complete-interface adequacy theorem (candidate)

Date: 2026-10-02
Status: Draft; theorem package in progress; no implementation authority
Scope: operational adequacy for the ordinary call/closure/Force/request/shallow-handler sublanguage
Depends on: `2026-10-02-ordinary-computation-semantics-package.md`,
`2026-10-01-coupled-effect-interface-core-draft.md`
Supersedes: none

## 1. The theorem target

The next result is one simulation theorem from source executions to complete
typed computation interfaces. It is not a separate theorem for each fixture or
Oracle routing case. It covers the supported source machine as one transition
system, with the same assignment `ν` and the same complete request/resumption
interface through evaluation, application, adaptation, `Force`, handler
search, and raw resumption.

The theorem preserves an already-derived callback capture incidence through
nested call/adaptation/`Force` transitions while its receiver and handler
remain active, as selected by the user. The selected candidate source relation
also makes an `E` request exposed by forcing a caller-owned thunk visible when
the callback's complete `CallView` is under a concrete capture contract that
exposes `E`. The contract, not `Force` or hidden provenance, supplies the
authority. Origin, dynamic event identity, and `K,D` remain unchanged. A
caller-owned request performed by the receiver's own body is outside that
callback boundary. Lineage alone grants no eligibility or mask, and no maker
activation survives return.

## 2. Complete operational observation

Fix an ownership derivation `σ` for source binders and an admissible complete
assignment `ν` to those binders. Write

```text
Execπ,σ,ν(e,C)
```

for the state-threaded source execution relation from configuration `C`. It
records returns, dynamic requests, every finite observable request prefix,
and the continuation of each request at the live resumed configuration. A
request observation retains the exact operation and payload, source origin,
dynamic event, candidate activation path, and its symbolic family facts `K`
with all dependent views in `D`. Latent closures and thunks retain their
complete future behavior relation; they are not collapsed to the requests
already emitted.

Let `Obsν(τ)` be the complete interface projection of one execution
observation `τ`. It includes value roots and every immediate, latent,
residual, continuation, and active-handler view that can affect a later source
transition. It projects away only proof labels that have no source observation;
the request-origin and handler-path incidences needed to replay a later
transition remain. `K` is interpreted under the same `ν` as the root and
request views, and `D` records which of those views still depend on each
predicate.

The source relation of a component is the collecting relation

```text
Semπ,σ(C) = { (ν,O) |
  ν is admissible under σ,
  τ is an observable execution of Execπ,σ,ν from C,
  O ∈ Obsν(τ)
}
```

For divergence, `τ` ranges over all finite observable prefixes. This makes
exact resumable execution the reference relation; a later finite presentation
may conservatively cover `Sem` without representing exact trace support.

The complete observation is contextual, not just the prefix already run. A
typed finite interaction may apply a returned closure to an admissible value,
force a returned thunk, dispatch a request, or resume a continuation with a
source-admissible response and reachable well-typed live state. `Obsν(τ)`
contains the outcomes of all such finite interactions at `ν`. This universal
future-use clause is guarded by the value/request constructor: entering a
closure, thunk, or continuation reveals its next source transition before
recursing. It preserves latent behavior without requiring inference to
represent exact trace support or continuation-use counts.

## 3. Adequacy statement

Let `P` be any complete-interface presentation assigned to `C`, with denotation
`⟦P⟧ρ` over the same imported identities `ρ`, source-owned assignment `ν`,
and complete observable root interfaces. The required adequacy condition is

```text
Semπ,σ(C) ⊆ ⟦P⟧ρ .
```

This is the soundness direction needed for final well-typed-program
acceptance. It is not an equality claim and does not impose exact
continuation-sensitive inference. The inclusion is fiberwise: the same `ν`
must witness the execution and the interface, and every symbolic family
predicate that remains incident to a root, request, residual, or continuation
must still hold in that fiber. A projection that changes `ν`, rebuilds `K`
after materializing the request family, or drops live `D` incidence does not
satisfy the condition.

Relate concrete configurations and complete interfaces by
`C Rν,σ,π I` when:

- their current source values, live stores, and ordered activations have the
  same well-typed observable interpretation at `ν`; and
- for every typed finite future interaction from `C`, the corresponding
  interaction from `I` has a matching source observation with the same result,
  request identity/origin/path, and joint `K,D` fiber.

For closures and thunks this quantifies over every source-admissible argument
and force position. For a suspended request it quantifies over every
source-admissible response and every reachable live resumed state satisfying
the same `ν`; it does not quantify over ill-typed responses or arbitrary store
corruption. Store writes, `OpCompat`, and re-entry must preserve this
admissibility. The relation compares future behavior, not only the currently
emitted prefix.

Write `Psrc(C)` for the syntax-directed transition system over complete
interfaces, initialized by an interface related to `C` and stepped by one
interface image `I ─#π,σ,ν→ I′` per source transition. `Psrc` has no finite
syntax or solver algorithm at this stage. An interface image is adequate only
when it provides forward coverage:

```text
C Rν,σ,π I ∧ C ─π,σ,ν→ C′
⇒ ∃I′. I ─#π,σ,ν→ I′ ∧ C′ Rν,σ,π I′
```

At a request suspension, the matching interface request must also carry a
continuation related by `R` for every typed admissible resumption. Exact
relational images satisfy coverage by construction; the theorem also permits
a conservative complete-interface image, but not an empty or partial one.
Later, a finite presentation must prove its denotation covers this transition
system and its universally quantified future-use relation.

## 4. Exact complete-interface embedding

The complete interface for this milestone is semantic and potentially
infinite; it is not yet the finite presentation used by an inference engine.
For a candidate source configuration `C` at assignment `ν`, define
`Eν,σ(C)` to contain its current value roots, live store, ordered activations,
lineage, typed request/resumption interface, and every latent closure/thunk
behavior under admissible future interactions. Request observations retain
the source origin, dynamic event identity, and joint `K,D` incidence. The
interface uses the same lexical binder map `σ` and assignment `ν` as the
source configuration. Its transition rules are the relational images of the
source rules described in the ordinary-computation package, with stateful
bind interpreted by the bind equations above.

**Theorem (source execution is simulated by the exact complete interface).**
For the candidate source machine, every well-typed configuration `C` has the
initial related interface `Eν,σ(C)`. Every source step
`C →π,σ,ν C′` has a matching interface image
`Eν,σ(C) →#π,σ,ν Eν,σ(C′)` and the successor remains related. This covers
every finite prefix, return, and request suspension. For every source-
admissible typed response and reachable well-typed resumed state at the same
`ν`, the interface continuation steps to the embedding of the source resumed
configuration. Thus the complete contextual relation is covered fiberwise,
including latent future use and resumptions.

The common invariant for every image step is:

1. **One assignment:** premises and conclusions use the same `ν`; independent
   source-owned identities are consistently renamed apart before composition,
   while source-shared identities remain shared.
2. **Request factorization:** each exposed request is either generated by the
   current source rule or inherited through a value/computation lineage. Its
   source origin is preserved in the inherited case; allocating a new dynamic
   event does not rewrite that origin.
3. **Joint family transport:** every live `K` predicate and its `D` incidence
   are composed with the views they constrain. A request being handled,
   delayed, absent from immediate support, or hidden by a residual projection
   does not discharge a formula that still constrains another view.
4. **Configuration fidelity:** state, ordered active frames, exact operation,
   per-event origin, and source handler-path evidence used by eligibility are
   those of the actual source configuration. An image step cannot synthesize
   eligibility from family equality.
5. **Resumption fidelity:** requests carry the actual continuation and live
   state. Bind appends to each resumption; shallow selection passes the raw
   continuation outside the selected handler; forwarding adds only the
   source-prescribed re-entry for still-enclosing handlers. A suspended
   invocation retains a re-entry wrapper even if search unwinds its active
   call-frame occurrence. Before the saved suffix runs, resumption installs a
   fresh/resumed occurrence; normal completion removes exactly that occurrence.
   The wrapper preserves live store and required lineage without reinstalling
   a consumed shallow handler or an exited maker handler. Lineage data alone
   does not implement this transition.

The owner-span realization in `2026-10-02-typed-source-owner-realization.md`
refines that wrapper premise. Both sides use its same control context:
borrowing an exact still-live owner does not pop it at span completion;
resuming code whose owner expired allocates a fresh execution occurrence
without renaming old value/evidence ownership. Intermediate completion
continues the captured parent suffix, and only the capture delimiter returns
to the current resumer. The exact-embedding argument copies this protocol
on both sides; it does not itself establish raw-source owner elaboration.

Typed-boundary §4's reviewed context-projection correction refines request
observation in the same way: both sides retain the executing typed view
delimiters at emission, before handler filtering, and their crossed scopes
on raw capture/resumption. Outward support is a separate projection. The
embedding uses this corrected candidate, not the superseded outward-only
observation definition. Its equality-of-projections argument does not require
a new finite-representation premise, and still does not prove raw-source
elaboration of the executable typed view positions.

### Proof

Relate `C` to `Eν,σ(C)` by equality of the source-observable projections and
the included complete future interaction relation. Initial relatedness is
therefore immediate and does not assume a separately chosen interface. Prove
the step clause by induction on the source transition derivation:

| Source transition | Complete-interface image |
|---|---|
| expression evaluation and return | project the same current value and live configuration |
| closure application | use the same lexical closure body, caller store and activations; push its invocation frame in both configurations. A suspended call carries the same re-entry wrapper through unwind and reinstalls only that invocation occurrence on resume |
| typed value adaptation | compose argument, call, and result relations with the same binder map `σ` and assignment `ν`; one map renames all type/effect/`K,D` views, so no endpoint is independently re-instantiated |
| thunk construction / `Force` | construction stores the latent relation; `Force` exposes its next request without changing origin or `K,D`. During an active concrete callback `CallView`, visibility comes from its declared capture contract for both direct and force-exposed requests |
| operation request | instantiate declaration binders using the request site's fixed lookup map; copy operation, payload, event identity, origin, and joint `K,D`; embed the same continuation |
| shallow-handler search | follow the same ordered active candidates, current concrete boundary and visibility evidence, selected arm or forwarding rule, and raw continuation; `OpCompat` checks selected arms without changing search |

For stateful sequencing, use the bind lifting lemma. In its return case,
source and interface apply their continuations to the same related value and
full live configuration. In its request case, both append the continuation;
after every admissible resumption the resumed pair lies in the finite
resumption closure used by the lemma. The same `ν` is used throughout, so
typed-family formulas remain joined with all dependent `D` views.

For closure/thunk future use, the complete interface stores the source
latent relation rather than only its emitted prefix. Any admissible
application/force is consequently another induction case above. This proves
the future-use clause by induction on the finite interaction context, nested
under the closure/thunk constructor; the next source transition is observed
before the induction recurs. For a suspended request, the interface stores
the actual continuation and live state. The resumption case quantifies over
the same typed response and resumed configuration on both sides, so it
reduces to the source transition simulation without an arbitrary-state or
store-snapshot premise. Shallow selection passes the raw continuation
outside the selected activation; forwarding adds only source-prescribed
re-entry for still-enclosing handlers. If search unwound an invocation frame,
its continuation wrapper reinstalls exactly the resumed occurrence before the
saved suffix and removes it on normal completion. No store snapshot or exited
handler is restored. Guarded coinduction over requests then proves resumption
preservation at the same `ν`.

This is an exact semantic embedding, not a finite solver construction. Its
adequacy follows from the explicit case simulation above; it makes no claim
that `Eν,σ(C)` has a finite representation or that a finite presentation is
principal. Those are the next milestone's proof obligations.

The exact embedding proves source adequacy only at the semantic carrier
level. In particular, it does not establish that a finite symbolic `P` can
present this relation or that a solver computes a principal one.

### Bind lifting lemma

This is the reusable composition result used by calls, adapters, and `Force`.
Write a source computation outcome as either

```text
Ret(v,C′)
Req(q,C′,k)       // k receives a typed response and the live resumed state
```

and define source bind by

```text
Ret(v,C′) >>= F  = F(v,C′)
Req(q,C′,k) >>= F = Req(q,C′, λ(r,C″). k(r,C″) >>= F)
```

The interface transition uses the same bind on interface outcomes. With
`σ` and policy `π` fixed, let `Simν(S,S#)` be the greatest relation such
that every source outcome has a matching interface outcome at the same `ν`.
A return matches related values and full configurations under `Rν,σ,π`,
including live stores, ordered activations, required lineage, and live `K,D`
incidences. A request matches operation, payload, origin, event path, and joint
`K,D`, with related suspension configurations; for every source-admissible
typed response and related reachable well-typed resumed configuration, its
continuation pair is again in `Simν`. This recursive requirement is guarded
by the matched request constructor.

**Lemma (bind preserves simulation).** Suppose `Simν(S,S#)` holds. Require
that, for every admissible related value/configuration pair `(v,C′)` and
`(v#,I′)` returned by related computations reachable from `S,S#` after any
finite sequence of admissible matched resumptions (including zero),
`Simν(F(v,C′),F#(v#,I′))` holds. The pair carries the full relevant
configuration under `Rν,σ,π`, not just its store. Then

```text
Simν(S >>= F, S# >>= F#)
```

Proof: take all related computation pairs reachable by finite admissible
matched resumptions, and form the candidate relation consisting of their
bound pairs together with the `Simν` pairs supplied by the next-computation
premise. In a return case at any such pair, that premise supplies simulation
of the next computations at the actual related value/configuration pair. In
a request case, both binds preserve the matched request and append `F/F#`
to its continuations. After every admissible matched resumption, the resumed
computation pair is again reachable, so its bound pair belongs to the
candidate relation. Thus the candidate satisfies the return clause and the
request clause with its recursive obligation beneath a request constructor;
guarded coinductive closure places it in the greatest relation `Simν`.
This includes requests whose continuations return only after further
resumptions. Live configurations are threaded through unchanged by bind;
source re-entry transitions remain explicit, with no store snapshot or reset.
The same `ν`, origin, and every still-live `K,D` incidence are preserved.

Relational composition is associative by reassociating intermediate related
value/configuration witnesses subject to the same reachable-return premise.
Consequently call-by-value application,
argument/result adaptation, and sequencing after `Force` are instances of
this lemma. It supplies composition only; atomic closure/handler/force images
are the separate cases in the exact-interface simulation proof in §4.

## 5. Why this is one theorem, not separate site rules

The proof has one invariant and one compositional image relation. Calls,
closures, adaptation, force, requests, and shallow handlers are cases of the
ordinary source transition system. Row union, filtering, and handler residual
support are projections after those relational images; they do not enter the
simulation proof as independent semantics. Callback capture is only one
receiver-local visibility premise for an event whose derivation crosses the
relevant typed callback boundary; receiver-body events use ordinary
visibility. Direct requests and requests exposed by `Force` within one
callback `CallView` use the same concrete capture contract, with event origin
and `K,D` kept distinct.

This theorem deliberately proves only source execution into the complete
relational carrier. It does not claim that a finite `P` exists, that a solver
computes the least representable `P`, or that generalization admissibility is
proved. Those are the next representation and principality gates.

## 6. Source ownership and scope of the result

### Selected lexical ownership for one scheme lookup

`σ` is the ordinary lexical type-binder environment, rather than a
request-family grouping mechanism:

1. A source lookup of a polymorphic value opens its scheme with one
   capture-avoiding substitution map. The map applies consistently to every
   occurrence of each binder across value types, latent effect views, request
   arguments, operation payload/results, and `K,D` endpoints.
2. Free/imported identities in the environment stay fixed. Distinct
   independent lookups receive disjoint local binders; sharing remains only
   where the source environment or a typing constraint relates them.
3. A resolved operation value uses one such map at source lookup. Its
   application and the thunk it constructs retain that typed instance;
   `Force` creates a dynamic event but does not instantiate declaration
   binders again. Repeated execution of one source site can therefore create
   distinct event IDs with the same static family arguments.
4. A handler arm resolves the same operation declaration under its own
   capture-avoiding map. `OpCompat` relates the complete request and arm
   instances; equal operation/family heads do not identify their binders.

This uses one lexical substitution law for values and effects and directly
preserves the same-binder invariant required by `K,D`. It is the source rule
of this candidate machine, not a claim that the current syntax reference or
retired F5 implementation already specifies effect generalization. It defines
lookup ownership only and does not claim a generalization theorem. No Oracle
routing behavior is used to derive it.

Generalization still requires its own admissibility theorem. A captured
mutable-cell witness shows that identities free in reachable shared-store
roots cannot be copied independently at external uses. The successor must
prove the complete admissibility condition, including effectful right-hand
sides; this package imports no value restriction and does not claim that
store-root exclusion alone suffices. Generalization must preserve source type
and store relations together.

The exact-interface theorem proves initial relatedness by choosing
`I₀=Eν,σ(C)` and proves every primitive image by case analysis on the
candidate source transition, using the table and the bind-lifting lemma in
§4. Its future-use proof opens each admissible closure/thunk interaction into
the same source rule cases; its resumption proof uses the same typed response,
live state, and `ν` on both sides. It therefore closes the source-to-exact-
interface adequacy milestone for this candidate semantics.

This exact interface is an extensional semantic object and may be infinite.
The result does not prove a finite `P`, a decision procedure, finite
principality, or that the current Yulang typing implementation realizes the
candidate source rules. In particular, effectful lookup/generalization is
outside the current syntax-reference authority; lifecycle admissibility for
shared stores and effectful right-hand sides remains Milestone 4. The next
gate is to derive a finite symbolic presentation of this exact relation and
prove soundness/principality relative to that presentation.

## 7. Status and next gate

This is a theorem package candidate, not an authoritative semantics. It
consolidates bind, adaptation, handler-image, ordered-search, and `K,D`
transport into one exact-interface simulation proof. Its first bundled review
found missing forward-coverage and future-use obligations; §4 now gives the
initial relation, primitive case simulation, and contextual future-use and
resumption argument for the candidate machine. The user's 2026-10-02 decision
closes imported-Force visibility: concrete typed callback visibility applies
uniformly to direct requests and requests exposed by `Force`, without
provenance-based veto or authority creation by `Force`. Ordinary escape
handling and preservation of established active incidence are also selected.
This closes Milestones 1–2 for the candidate semantics at the exact
relational-carrier level.

The remaining source-language gap is whether an Authoritative Yulang
typing/evaluation relation supplies the candidate lookup ownership and every
transition listed in §4. This exact interface may be infinite; the result
does not prove a finite symbolic presentation, a decision procedure, or
principality. Milestone 3 must construct that presentation and prove its
soundness/principality, or identify one precise obstruction. No compiler
implementation or tests follow from this draft.

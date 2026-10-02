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
remain active, as selected by the user. Origin and `K,D` remain unchanged;
lineage alone grants no eligibility or mask, and no maker activation survives
return. It is parametric in the remaining milestone-1 choice of whether
forcing a caller-owned thunk during callback execution creates a new
receiver-local incidence or only transports one already established. The
preservation instruction alone does not decide creation.

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

## 4. Compositional simulation theorem

**Theorem (ordinary source execution is simulated by complete interfaces).**
Fix `π`, `σ`, `ν`, and a source-well-typed initial configuration `C`. Suppose
there is an initial interface `I₀` with `C Rν,σ,π I₀`, and forward coverage
holds for every primitive transition in the supported machine: expression
execution, stateful bind, closure application, typed value adaptation, thunk
construction/`Force`, operation request, and shallow-handler search. Then
every finite source execution prefix, return, and request suspension has a
matching path in `Psrc(C)`, and each matching state remains related by `R`.
Every typed resumption of a matched request extends both paths while preserving
`R` and the same `ν`. Consequently the contextual source relation is covered
fiberwise by the complete-interface transition system.

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

### Proof

Use guarded coinduction on `R`, with induction on the finite interaction
context exposed at each guard. For each source step, apply forward coverage to
obtain the matching interface step and successor relation. A value/return
step uses the identity image. Source sequencing is relational composition at
the shared intermediate value and configuration. The return bind clause
composes the next computation; the request bind clause preserves the request
and maps the appended computation into its saved continuation. At suspension,
use the resumption clause of `R` for each source-admissible response and
reachable live state. It supplies the next related configurations without
resetting state or changing origin. Where search unwound an invocation frame,
primitive coverage must image its continuation wrapper installing a
fresh/resumed occurrence before the saved suffix and `ReturnFromInvocation`,
and removing exactly that occurrence on normal completion. This obligation
cannot be discharged by lineage preservation alone or by reinstating the
selected shallow handler or exited maker handlers.

The application rule is the composition of callee evaluation, argument
evaluation, and `ApplyValue`. Function adaptation is itself a composition of
argument adaptation, call, and result adaptation. The identity, forced,
delayed, and thunk-to-thunk cases all use the same typed-boundary image; a
force exposes the latent source computation only at that transition. By the
induction hypotheses and clauses 1–3 of the invariant, every request and its
family incidence is present in the composed image at the same assignment.

For a shallow handler, induct on ordered search and the source arm list.
Pattern and guard computations compose before the next arm decision. A
selected arm is imaged outside the selected activation and receives the raw
continuation. A forwarded request advances to the next active candidate and
adds the source-defined re-entry to the saved continuation. Every resumed
suffix therefore re-enters the same simulation relation at its actual
configuration. Clause 4 preserves candidate-specific eligibility, and
clause 5 preserves the raw suffix. The proof uses the handler transition
itself; it does not infer subtraction from immediate support.

The future-use clause of `R` handles latent closure and thunk behavior and
request continuations; finite-prefix induction alone would not establish
those observations. The final fiber condition follows from clauses 1 and 3:
every composed predicate is interpreted under the single joined assignment
and remains attached to every dependent output view. This proves the
conditional simulation claim.

## 5. Why this is one theorem, not separate site rules

The proof has one invariant and one compositional image relation. Calls,
closures, adaptation, force, requests, and shallow handlers are cases of the
ordinary source transition system. Row union, filtering, and handler residual
support are projections after those relational images; they do not enter the
simulation proof as independent semantics. Callback capture is only one
receiver-local visibility premise for an event whose derivation crosses the
relevant callback boundary; receiver-body events use ordinary visibility.
Capture creation follows fixed policy parameter `π`, while already-derived
incidence preservation is selected.

This theorem deliberately proves only source execution into the complete
relational carrier. It does not claim that a finite `P` exists, that a solver
computes the least representable `P`, or that generalization admissibility is
proved. Those are the next representation and principality gates.

## 6. Exact closure boundary

The proof above is a conditional simulation theorem. Its application to
Yulang source semantics is not yet certified. The imported-thunk
incidence-creation policy must be selected, and the primitive forward-simulation clauses and initial relation must then be proved:

- Every primitive transition must preserve the lexical binder map `σ` on
  lookup, application, callback, recursive root, and request occurrence.
  The selected map is capture-avoiding and shared across each declaration
  binder's value, latent effect, payload/result, and `K,D` occurrences;
  `Force` does not instantiate again. This is a source rule of the candidate
  machine, not a request-family grouping rule. The full admissibility of
  generalization across stores/effectful right-hand sides remains in the
  later lifecycle theorem.
- The selected `Capture` incidence must be shown to follow the complete
  source `CallView` through every callback call/adaptation/force transition.
  Preservation of an established incidence is selected; creation for a
  caller-owned thunk forced during callback execution remains the single
  policy choice. Coverage must be proved for whichever policy is selected.

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
preserves the same-binder invariant required by `K,D`. It is the selected
source rule for this candidate machine. The syntax reference and retired F5
implementation do not establish effect generalization; this rule defines
lookup ownership only and does not claim a generalization theorem. No Oracle
routing behavior is used to derive it.

Generalization still requires its own admissibility theorem. A captured
mutable-cell witness shows that identities free in reachable shared-store
roots cannot be copied independently at external uses. The successor must
prove the complete admissibility condition, including effectful right-hand
sides; this package imports no value restriction and does not claim that
store-root exclusion alone suffices. Generalization must preserve source type
and store relations together.

### Selected preservation and remaining incidence-creation choice

An already-derived `Captureν(q,h)` incidence is preserved through nested
calls, adaptation, and `Force` while the same `(r,a,h)` is active. It applies
only to a source derivation crossing callback argument boundary `a` toward
`h`; a request generated by the receiver's own body follows ordinary ordered
handler visibility. Handler ownership, family equality, wildcard rows, and
residual upper bounds cannot establish incidence. The event retains origin,
identity, and joint `K,D`. No exited activation is restored, and retained
lineage creates neither a grant nor a maker mask.

For a caller-owned thunk forced during callback execution, the remaining
milestone-1 choice is (A) create a new receiver-local incidence when its exact
operation is admitted, or (B) preserve only an incidence already established
by the callback-boundary derivation. The user's preservation choice does not
by itself reject either creation policy. The simulation schema fixes one
policy as a parameter and requires coverage for that policy. Ordinary caller
handling after maker return is already selected under both alternatives.

Closure and thunk re-entry uses the current caller's live store and ordered
active source activations, pushing/popping only the current invocation frame.
A suspended invocation carries its re-entry wrapper through search unwind;
resumption reinstalls a fresh/resumed call-frame occurrence before its saved
suffix, and normal completion removes precisely that occurrence. Coverage
must prove these transitions preserve the actual live store and required
lineage without reinstating consumed shallow or exited maker handlers.
Lineage data alone does not supply frame re-entry. Existing active incidence
is preserved only under its already-stated activation premises. At dispatch, coverage must match the actual `C_h`: ordered
search reaches `h`, every applicable current boundary admits the event, the
exact operation is covered, and the selected arm satisfies `OpCompat`.
Maker expiry removes maker premises only; unrelated active boundaries remain.

The local simulation relation `R` also has to be realized concretely for
closures, thunks, and resumptions. The proof must show that every source step
has an interface image, and that related returned values quantify over all
typed future uses. Merely preserving the five coordinates below is
insufficient: an image that omits a latent closure request can preserve current
state/origin/formulas and still fail when the closure is later called. Likewise,
resumption quantification is over source-admissible responses and reachable
well-typed stores at the same `ν`, not arbitrary responses or corrupted
states. `OpCompat`, store preservation, and frame re-entry must establish that
the admissibility premise survives each resume.

The ownership draft also needs the generalization-admissibility theorem: a
scheme may freshen only the binders its source boundary permits, and no binder
still shared with a reachable mutable store may be copied independently. This
is an ownership/lifecycle condition on the same complete relation, not a
per-fixture special case. Its exact source boundary is not determined by the
current pure F5 contract.

These are source-semantics premises, not solver implementation gaps.
Conditional relational transport is available for any fixed `σ`; no theorem
can show that a successor inference result preserves Yulang's intended
sharing until the source relation defines it. Likewise, exact image
construction by definition would make forward coverage vacuous and certify
no finite inference procedure. The next proof must discharge the displayed
simulation obligations for the selected source rules, not rename them as
invariants. No Oracle routing rule supplies missing authority.

## 7. Status and next gate

This is a theorem package candidate, not an authoritative semantics. It
consolidates existing bind, adaptation, handler-image, ordered-search, and
`K,D` transport evidence into one simulation argument. Its first bundled
review found missing forward coverage and future-use obligations; the
relation above is the repair. The remaining milestone-1 decision is the imported-thunk incidence-creation
choice above; ordinary escape handling and preservation of established active
incidence are selected. A subsequent delta review should inspect the selected
clause and its dependent coverage obligations without restarting fixture-level
reviews. The conditional schema proves no primitive coverage, initial
relation, universal future-use premise, or admissible-resumption premise by
itself; those remain proof obligations before adequacy can close.

No compiler implementation or tests follow from this draft. After source
semantics is fixed, the next task is to instantiate the theorem against every
supported transition in the ordinary machine and either close adequacy or
exhibit a concrete source execution not covered by the complete interface.
Only then derive and prove the finite presentation and its principality.

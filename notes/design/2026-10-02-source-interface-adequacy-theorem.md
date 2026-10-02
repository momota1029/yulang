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

The theorem is parameterized by a callback-capture policy `π` only at the
receiver-local incidence point. This keeps the operational simulation and
`K,D` transport proof independent of the still-open choice about a
caller-owned thunk forced during a callback. Specializing `π` changes which
receiver-local handler transitions are available and therefore can change a
handler image; it does not change origin preservation, ordinary post-escape
caller search, or the shared-assignment composition laws. This parameterization
is proof factoring, not approval of either policy.

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

Write `Psrc(C)` for the syntax-directed, generally infinite relational image
obtained by interpreting the source transition clauses on complete interfaces
with relational composition, request/resumption images, and handler images.
It has no finite syntax or solver algorithm at this stage. The theorem below
targets `Psrc`; a later finite presentation must prove that its denotation
covers every source observation represented by this image.

## 4. Compositional simulation theorem

**Theorem (ordinary source execution is covered by its complete relational
image).** Fix `π`, `σ`, `ν`, and a well-formed initial configuration `C`.
Interpret each primitive source transition by its relational image on complete
interfaces. Use one image operator for ordinary expression execution,
stateful bind, closure application, typed value adaptation, delayed-value
construction/`Force`, operation requests, and shallow-handler search. If each
primitive transition obeys the common interface invariant below, then every
finite source execution prefix, request suspension, request resumption, and
return from `C` is represented in `Psrc(C)`. Therefore
`Semπ,σ(C) ⊆ ⟦Psrc(C)⟧ρ` for all source programs in the supported sublanguage.

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
   source-prescribed re-entry for still-enclosing handlers.

### Proof

Induct on finite source execution derivations, with the request continuation
case quantified over every response and live resumed state. A value/return
step is represented by the identity interface image. Source sequencing is
represented by relational composition at the shared intermediate value and
configuration. The return bind clause composes the next computation; the
request bind clause keeps the request and maps the appended computation into
the saved continuation. Thus the induction hypothesis applies after every
resume without resetting state or changing origin.

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

The argument applies to each finite prefix of a divergent execution. These
prefix results jointly cover every finite observable behavior used by
`Sem`. The final fiber condition follows from clauses 1 and 3: every composed
predicate is interpreted under the single joined assignment and remains
attached to every dependent output view. This proves the simulation claim.

## 5. Why this is one theorem, not separate site rules

The proof has one invariant and one compositional image relation. Calls,
closures, adaptation, force, requests, and shallow handlers are cases of the
ordinary source transition system. Row union, filtering, and handler residual
support are projections after those relational images; they do not enter the
simulation proof as independent semantics. Callback capture is only one
candidate-specific visibility premise for a receiver-local handler. The
policy parameter `π` is fixed across the whole derivation and cannot be
changed by a later phase.

This theorem deliberately proves only source execution into the complete
relational carrier. It does not claim that a finite `P` exists, that a solver
computes the least representable `P`, or that the source typing/ownership
rules have already been selected. Those are the next representation and
principality gates.

## 6. Exact closure boundary

The proof above is closed for the relational image *once the five invariant
clauses are the source transition contract*. Its application to Yulang source
semantics is not yet certified. Two premises must be made source-derived in
the frozen machine:

- The source typing derivation must say which operation-declaration binders
  are shared across each call, callback, recursive root, and request
  occurrence. The current syntax reference does not specify effect-inference
  ownership, and the candidate core explicitly leaves this rule open. Without
  it, `σ` and the source-induced sharing presented by `D` are parameters, not
  a Yulang theorem.
- The receiver-local `Capture` incidence for a caller-owned thunk forced
  during callback execution remains the unresolved choice in the milestone-1
  source package. The simulation proof is uniform in `π`, but handler-image
  adequacy for Yulang must specialize one policy before this transition case
  can be certified.

These are source-semantics premises, not solver implementation gaps. The
first is the larger adequacy dependency: typed-family transport can be proved
for any fixed source ownership relation, but no theorem can show that the
successor inference result preserves Yulang's intended sharing until the
source relation defines that sharing. No Oracle routing rule supplies this
missing authority.

## 7. Status and next gate

This is a theorem package candidate, not an authoritative semantics. It
consolidates existing bind, adaptation, handler-image, ordered-search, and
`K,D` transport evidence into one simulation argument. A bundled theorem
review should test the whole statement after the source ownership rule and
callback/`Force` policy are fixed; do not restart fixture-level reviews.

No compiler implementation or tests follow from this draft. After source
semantics is fixed, the next task is to instantiate the theorem against every
supported transition in the ordinary machine and either close adequacy or
exhibit a concrete source execution not covered by the complete interface.
Only then derive and prove the finite presentation and its principality.

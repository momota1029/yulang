# Source-to-complete-interface adequacy

Date: 2026-10-02
Branch: `research/simple-sub-intrusion`
Status: theorem package candidate; no implementation authority

The ordinary escaped-closure caller-search consequence is settled independently
of receiver-local capture: after maker return, dispatch uses the current
caller's ordered active handlers and applicable source boundaries at the
actual post-application configuration. No maker capture premise or historical
mask is carried into the call. Operation-value application constructs a
thunk, with source-demanded `Force` exposing its request.

The next milestone is consolidated in
`notes/design/2026-10-02-source-interface-adequacy-theorem.md`. It states one
fiberwise simulation for the supported ordinary machine. Its invariant keeps
one assignment `ν`, each request's own origin, all live `K,D` incidences, the
actual ordered handler configuration, and raw resumptions with live state.
Calls, closures, adaptation, `Force`, and shallow handlers are cases of the
same relational image; support projection follows that image.

The user has now fixed the source principle: visibility comes from the
concrete typed callback boundary visible during its complete `CallView`.
Thus a caller-owned thunk's request, when exposed by `Force` in that view and
admitted by the concrete contract, is eligible like a direct callback
request. `Force` reveals latent computation and creates no authority; caller
origin, event identity, and `K,D` remain intact. Wildcard rows, family
equality, surface rows, and handler ownership alone grant no incidence. The
incidence ends with its receiver/handler activation. The theorem is no longer
parametric in this choice; coverage must establish this equation.

A bundled architect/compiler-referee/spec-auditor review found two gaps in the
first theorem statement: its five identity-preservation clauses did not require
forward coverage of concrete transitions or latent future behavior, and its
resume quantifier admitted untyped responses/corrupted stores. The repaired
statement defined `R` by typed future interactions, required one matching
interface successor for every source transition, and restricted resumes to
source-admissible responses and reachable well-typed live states at the same
`ν`. At that stage the result was only a conditional lifting theorem. The
second bundled review found no residual issue in that scope. A later
exact-interface embedding in the theorem design instantiates initial
relatedness, primitive images, future use, and resumption preservation for the
candidate machine; it remains an infinite semantic model rather than a finite
presentation.

The focused dependency search found a broader source-semantics premise: the
source typing relation must define which operation-declaration binders are
shared across calls, callback uses, recursive roots, and request occurrences.
The syntax reference for effect rows explicitly leaves effect inference and
row meaning out of scope; the coupled-interface core also leaves the
source-derived sharing rule open. Consequently, `σ` and `D`'s source sharing
are still inputs to the adequacy package. Typed-family transport can be
proved for a fixed ownership relation, but the current evidence cannot show
that it is the current Yulang relation. This remains a source-authority gap
for claiming final Yulang acceptance, while the finite presentation can be
derived relative to the explicit candidate ownership map.

The theorem now includes a candidate lexical ownership rule: one
capture-avoiding substitution map per source scheme lookup, consistently shared
across all value/effect/family views; fixed free/imported identities;
monomorphic parameters; open internal SCC uses; independent external-use
freshening; and no freshening merely from dynamic `Force`. This is the smallest
unified candidate found. No current Authoritative source rule decides
operation-binder lookup/application or typed effect generalization. The
syntax-reference pages explicitly exclude those meanings, and F4/F5 do not
cover effectful application; F5 remains legacy comparison material. The
theorem therefore proves adequacy for the candidate source machine, not yet
that its binder ownership matches the intended Yulang source relation.

The theorem package now contains a reusable stateful bind lifting lemma for
calls, adaptation, and sequencing after `Force`. An independent compiler-
referee delta review found and repaired the prior gap where the next
computation was constrained only on immediate returns, leaving returns after
resumption uncovered. The final premise quantifies over every related
value/configuration pair reachable after any finite sequence of admissible
matched resumptions, including zero; configurations retain the same `ν` and
full live `K,D` incidence. Guarded closure then covers nested requests. The
lemma supplies composition. The exact-interface embedding proof later
discharges the candidate machine's initial relation, atomic images, and
admissible future/resumption cases by explicit source-rule simulation.

An adversarial store-sharing witness found that freshening the type of a
captured mutable cell at each external use is unsound. The candidate now keeps
identities free in reachable shared-store roots fixed, uniformly across value,
effect, and `K,D` views. Focused referee and spec-auditor delta reviews found no
residual issue in that clause; neither review treats it as a complete
effectful generalization theorem. Whether and where an effectful right-hand
side may generalize remains open for the lifecycle theorem.

The user's decisions select preservation of an already-derived callback
incidence through nested active call/adaptation/Force transitions, ordinary
caller search after escape, and uniform concrete-boundary visibility for
direct and caller-thunk requests within a callback `CallView`. The current
source package records this rule without adding a `Force` authority construct
or reopening settled escape cases. The
bundled package review repaired event-relevant callback boundaries, ordinary
handling for receiver-body events, actual-`C_h` boundary checks, and concrete
closure-frame re-entry using the caller's current store and activations. A
focused referee delta then required invocation re-entry across handler unwind:
suspension retains a wrapper, resume reinstalls the invocation occurrence
before its saved suffix, and return removes exactly that occurrence without
restoring consumed shallow or maker handlers. The user's later A decision is
now stated as visibility from the concrete callback type for direct and
Force-exposed requests, with no provenance veto or Force-created authority.
The focused compiler-referee delta found no major issue. A package-level
compiler-referee review also found no major gap in the exact semantic
embedding: `I₀=Eν,σ(C)` supplies initial relatedness; source-rule cases cover
primitive images; latent relations and matched typed resumptions close
future-use. This is an exact, potentially infinite semantic interface, not a
finite solver result and not evidence that the current Yulang typing rules
already realize the candidate machine. Milestones 1–2 are closed for the
candidate semantics; next derive the finite symbolic presentation and prove
soundness/principality. The implementation-feasibility gate remains after
lifecycle preservation.

No compiler code or tests changed/run.

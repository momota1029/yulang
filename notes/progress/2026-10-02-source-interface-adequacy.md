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

The proof is policy-parametric in receiver-local `Capture` for a caller-owned
thunk forced during a callback. This lets the relational composition and
symbolic transport proof proceed without silently selecting that source
semantics. It does not certify the Yulang theorem before one policy is fixed.

A bundled architect/compiler-referee/spec-auditor review found two gaps in the
first theorem statement: its five identity-preservation clauses did not require
forward coverage of concrete transitions or latent future behavior, and its
resume quantifier admitted untyped responses/corrupted stores. The repaired
statement defines `R` by typed future interactions, requires one matching
interface successor for every source transition, and restricts resumes to
source-admissible responses and reachable well-typed live states at the same
`ν`. It now proves only the conditional lifting theorem from these premises.
The second bundled review found no residual issue in that scope. It does not
prove primitive coverage, establish `R` for Yulang values, or certify a finite
presentation.

The focused dependency search found a broader source-semantics premise: the
source typing relation must define which operation-declaration binders are
shared across calls, callback uses, recursive roots, and request occurrences.
The syntax reference for effect rows explicitly leaves effect inference and
row meaning out of scope; the coupled-interface core also leaves the
source-derived sharing rule open. Consequently, `σ` and `D`'s source sharing
are still inputs to the adequacy package. Typed-family transport can be
proved for a fixed ownership relation, but the current evidence cannot show
that it is the Yulang relation. This is the principal theorem blocker before
finite presentation and principality.

The theorem now includes a candidate lexical ownership rule: one
capture-avoiding substitution map per source scheme lookup, consistently shared
across all value/effect/family views; fixed free/imported identities;
monomorphic parameters; open internal SCC uses; independent external-use
freshening; and no freshening merely from dynamic `Force`. This is the smallest
unified candidate found, but no current Authoritative source rule decides
operation-binder lookup/application or typed effect generalization. The
syntax-reference pages explicitly exclude those meanings, and F4/F5 do not
cover effectful application; F5 remains legacy comparison material. The
candidate therefore still needs user approval before the theorem can be
instantiated for Yulang.

An adversarial store-sharing witness found that freshening the type of a
captured mutable cell at each external use is unsound. The candidate now keeps
identities free in reachable shared-store roots fixed, uniformly across value,
effect, and `K,D` views. Focused referee and spec-auditor delta reviews found no
residual issue in that clause; neither review treats it as a complete
effectful generalization theorem. Whether and where an effectful right-hand
side may generalize remains open for the lifecycle theorem.

The user's decisions select preservation of an already-derived callback
incidence through nested active call/adaptation/Force transitions and ordinary
caller search after escape. They do not conclusively select whether forcing a
caller-owned thunk creates a new incidence. The current package records this
single A/B source-policy choice without reopening settled escape cases. The
bundled package review repaired event-relevant callback boundaries, ordinary
handling for receiver-body events, actual-`C_h` boundary checks, and concrete
closure-frame re-entry using the caller's current store and activations. A
focused referee delta then required invocation re-entry across handler unwind:
suspension retains a wrapper, resume reinstalls the invocation occurrence
before its saved suffix, and return removes exactly that occurrence without
restoring consumed shallow or maker handlers. Review found this coherent; it
remains a forward-coverage obligation, not a completed adequacy proof. The
conditional schema still lacks primitive coverage, initial `R`, and universal
future-use/resumption realization. Resolve the single source choice, close
that theorem package, then move to the finite constrained-interface
soundness/principality theorem. The implementation-feasibility gate remains
after lifecycle preservation.

No compiler code or tests changed/run.

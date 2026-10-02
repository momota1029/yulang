# Source-to-complete-interface adequacy

Date: 2026-10-02
Branch: `research/simple-sub-intrusion`
Status: theorem package candidate; no implementation authority

The ordinary escaped-closure caller-search consequence is now isolated from
the receiver-local capture question. After maker return, dispatch uses the
current caller's ordered active handlers and their source boundary path; no
maker capture premise or historical mask is carried into the call. The
ordinary machine's operation-value application also constructs a thunk, with
the source-demanded `Force` exposing its request.

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

No compiler code or tests changed/run. The next semantic work is to derive the
ownership relation from source typing declarations and the already-reviewed
Simple-Sub/type-variable lifecycle, then review the complete adequacy package
once. The implementation-feasibility gate remains after the lifecycle theorem
milestone.

# Successor implementation feasibility checkpoint

Date: 2026-10-02
Branch: `research/simple-sub-intrusion`
Status: read-only architecture audit; no implementation authority

## Result

The selected nested-capture preservation clause is not currently implementable
as an end-to-end Yulang3 feature without substantial front-end and effect-model
work. The obstacle is not the ability to store another solver relation: the
current compiler surface does not represent the source transitions that the
proof obligation quantifies over.

Repository evidence:

- `crates/yu-hir/src/lib.rs::HirExpr` retains syntax-associated operator
  applications as `Apply`, so the parser/association layer has a useful
  application-shape substrate. The later source-resolved
  `crates/yu-hir/src/module.rs::ResolvedExpr` currently has only `Lambda`,
  `Integer`, `Name`, and `Error`; it has no resolved call/application, typed
  thunk/force, operation request, handler, or resumption nodes. `HirExpr::Apply`
  is syntax association data, not a resolved evaluation or inference step.
- `crates/yu-solver/src/lib.rs::Collector::emit_lambda` handles a narrow set
  of lambda bodies (parameter name, integer, resolved name); its other shapes
  return without a lambda recipe. There is no call or handler transition to
  attach the selected `Visible` preservation law to.
- `crates/yu-types/src/lib.rs` has polarized Function nodes with argument and
  result effect endpoints, but closed `PositiveEffectView` and
  `NegativeEffectView` expose only `Bottom` and `Empty`. This is insufficient
  to publish the successor's nonempty typed request rows and symbolic family
  constraints.
- `crates/yu-solver/src/lib.rs` already has a bounded substrate—polarized
  terms, value/effect variables, levels, directed bounds, extrusion, typed
  pairs, and F5 generalization/instantiation. This is useful characterization
  and possible migration substrate; it does not implement the successor
  `Rel_C`, callback origins, handler search, or `K,D` symbolic lifecycle.
- The current closed-scheme substitution in
  `crates/yu-solver/src/f5c_binder_substitution.rs` traverses Function value
  argument/result edges, but reconstructs effect fields as `Empty` / `Bottom`.
  The current representation therefore cannot serve as a direct implementation
  of uniform typed-family/effect transport; it would need a new carrier or a
  reviewed replacement of the F5 path, not a thin reuse of its binder walker.

## Feasibility classification

| Slice | Current feasibility | Evidence / boundary |
| --- | --- | --- |
| Pure finite SCC parent-map prototype | Plausible as an isolated research model after its theorem fixes the parent ports and observations | Existing polarized graph and SCC machinery provide useful input/output handles, but the current F5 publication contract is explicitly not the successor target. |
| Symbolic typed-family transport through solving and SCC lifecycle | Not ready to implement | The successor obligation identity, denotation, solving/residualization transitions, and parent quotient remain candidate mathematics; inventing storage now could freeze a representation before the proof. |
| Nested callback capture preservation in compiler | Not presently expressible end to end | HIR and source collection lack calls, handlers, force, and resume, while closed effect schemes cannot retain nonempty typed rows. |
| Full successor replacement | Large cross-layer change | Requires source syntax/HIR/evaluation interfaces, effect denotation and principal finite presentation, solver/lifecycle transport, then runtime/compiler integration and method/role/impl gate. |

The safe implementation conclusion is therefore **defer compiler changes for
the current preservation proof gate**. The existing graph substrate offers
some useful ownership/arena patterns, but its current scheme substitution
erases precisely the effect payloads that the successor must transport.
Continue alternating theory work with read-only code feasibility checks. Once
a narrow mathematical slice is
reviewed and implementation authority exists, prefer an isolated Rust
executable characterization over a Python side model, then assess whether it
maps to the existing solver substrate before changing production paths. This
checkpoint does not authorize that model or any compiler edit.

## Next gate

Return to the source call/handler relation and prove the composition premises
for callee/argument evaluation, both adaptations, callback origin, force,
ordered search, and raw resume. After each closed semantic slice, inspect the
corresponding HIR/solver/type representation and record whether it is directly
implementable, needs a bounded prototype, or requires a larger architecture
change. Method selection, roles, and implementation resolution remain a later
mandatory gate.

## Alternating proof / feasibility check: event identity

The callback-origin proof now distinguishes four coordinates: a static source
site template, an individual dynamic request event, the source computation or
callback/thunk value lineage, and an activation identity. Repeated execution
may create a new event from the same template and lineage; symbolic type
transport changes typed endpoints and `K,D`, not runtime event or activation
IDs. A delta review of this distinction found no issue. This closes only the
identity bookkeeping question, not the conditional source `Force` /
`B_{S,T}` preservation premise or the full soundness and principality proof.

The corresponding code check found no existing representation for source
origins, callback/thunk lineage, or these activation coordinates. Syntax HIR
does retain associated operator applications, but the resolved HIR and solver
collection path have no call/handler/force semantics to attach lineage to; the
current closed effect views also remain singleton `Bottom` / `Empty`. So the identity
distinction can be described in the proposed relational interface, but there
is no present compiler path where it can be implemented or exercised. This
reinforces the current decision to alternate proof slices with read-only
feasibility checks and defer production changes until the semantic carrier is
settled and implementation authority is granted.

## Alternating proof / feasibility check: request lineage

The returned-thunk discriminator was independently reviewed. The proof now
requires origin per exposed request, so a callback-created wrapper that forces
a caller-owned thunk cannot relabel its inner requests, and a mixed thunk must
retain separate origins and `K,D` incidences. The source value/force relation
must establish those facts; a single callback-owned bit on the thunk would be
unsound for caller hygiene.

The corresponding implementation check found no request-origin or
per-request typed-incidence carrier in resolved HIR, solver values, or closed
types. Syntax `HirExpr::Apply` carries its operator, operands, and source range,
but is not lowered into a resolved call node; source ranges also cannot serve
as dynamic request-event or activation identities. The core and both backend
crates likewise have no request/continuation, force, handler-frame, or thunk
runtime forms to reuse; the three `yu-core` / VM / native entrypoint source
files are currently crate-level documentation only. This is a broader gap than adding one callback flag:
the future carrier must survive value flow, wrappers, force, mixed
computations, and continuation resumption. No production code was changed;
this is not ready for a bounded compiler implementation.

The follow-up source check re-confirmed that the resolved `ResolvedExpr` is
the only matching expression declaration in the current HIR/solver/type/core/
backend slice, and it contains no `Force` or handler transition. `yu-core`,
VM, and native crate entrypoints remain one-line module docs. Thus the new
origin-indexed force/catch distinction has a mathematical home in `Run`,
`Visible`, and the latent interface candidate, but no existing execution
surface to host a prototype. This remains a theory-only step pending a settled
source relation and implementation authority.

The identity-map check found one limited reusable coordinate: resolved
`Lambda`/`Integer`/`Name`/`Error` expressions carry artifact-branded
`HirOccurrenceId`s. That is a compile-time occurrence identity, not a dynamic
request or activation ID. `HirExpr::Apply` currently has only operator,
operands, and source range, so even its call-site occurrence is not yet in the
resolved form. No event/activation allocator or transport path exists in the
runtime stubs. The candidate transport split therefore has a plausible
static-occurrence anchor for some existing nodes, but no end-to-end mapping
for call/force behavior.

The scheme-transport check confirms the gap extends into substitution:
`f5c_binder_substitution.rs` walks current positive/negative type nodes but
rebuilds Function effect endpoints as singleton `Bottom`/`Empty`; it has no
owned-occurrence or origin map. Thus the existing substitution cannot realize
the origin-labeled `Tr_θ`/bind equation, even if a source request node were
added above it. A successor needs a jointly transported type/formula,
occurrence-owner, and compile-time boundary map before its finite schemes can
preserve this evidence.

One naming collision is not reusable: `PhysicalOwnerKind` in
`f5c_draft_heap.rs` classifies vector-allocation accounting for the F5c
resource ledger. It is not a semantic owner of a request, family formula, or
`D` incidence. The existing HIR occurrence identity is a possible static
label substrate only; source-owner and handler-boundary maps still need new
typed carriers in a successor.

No source code was changed. No tests or builds were run.

The source-capture projection was checked against the resolved HIR and runtime
surface again while reviewing the theory slice. No source call/Force/effect
execution forms or runtime activation identity exist there, and current scheme
substitution still drops effect endpoints and has no origin map. The exact
receiver-contract incidence is therefore not incrementally hostable in the
current representation; implementing it now would require the unproved source
relation plus major front-end, solver, scheme-transport, and runtime work. Keep
this gate theory-only and repeat feasibility review after ordinary handler and
callback composition rules settle.

The follow-up Capture-join review inspected resolved HIR, solver, core, VM,
and native entrypoints again. `ResolvedExpr` remains limited to lambda,
integer, name, and error; `yu-core` and both backends still have no execution
forms for calls, Force, requests, or handler activations. The current solver
still exposes no origin/handler transport path. No small implementation slice
can realize this relation end to end; a prototype would prematurely require
the unresolved source judgment and substantial cross-layer architecture. No
code or tests were changed or run.

The closure-transport slice has one limited HIR substrate: `ResolvedExpr`
contains `Lambda` with an occurrence, parameter, and body, and the collector's
`emit_lambda` handles only parameter identity, integer, or resolved-name
bodies. It still has no resolved application node or source execution relation
for a closure call; `yu-core`, VM, and native remain boundary stubs. Thus closure
creation can be represented for narrow collection cases, but the reviewed
`Tr_θ`/captured-environment/re-entry equation cannot be exercised end to end.

## Alternating proof / feasibility check: imported Force under callback contract

The source proof review exposed a contract-scope distinction not settled by the
selected rules. An explicit callback `[F]` contract may either derive a new
capture-incidence edge for an inherited caller request executed by `Force`, or
leave that request at its imported caller boundary unless a separate contract
connection exists. Both candidates preserve caller origin and symbolic `K,D`;
they differ in whether the receiver handler consumes the request or forwards
it to an outer handler. Preserve-through-nested-receiver applies to an already
derived edge and family equality alone grants none, so neither decision selects
this case. The frozen source reference does not settle it. Independent
architectural, compiler-referee, and source-contract reviews agree that this
must remain an explicit source-rule question; the corresponding counterexample
must keep origin fixed and vary only the contract-incidence rule.

The implementation check found that both candidates use the same missing
cross-layer carrier: per-request source origin plus a separate handler capture
incidence and the dependent typed-family predicate. Their difference belongs
in source `Force`/callback relation derivation, not in a new row encoding. The
current resolved HIR has no application, Force, or handler transition, and the
scheme path cannot retain the necessary effect interfaces, so neither candidate
supports a bounded end-to-end compiler prototype. Defer production changes
until the source rule is selected and its relation is proved. No tests or builds
were run.
The next plausible implementation checkpoint is after the ordinary resolved
call and value/environment relation exists; no code change is authorized now.

The active-frame/escape corollary also has no executable host yet: current
resolved HIR has no handler construct or call transition, and the VM/native
crates expose no activation-stack push/pop/resume path. Existing static
`HirOccurrenceId` cannot represent a runtime handler activation or prove that
normal return removes exactly that activation while continuation resume
restores it. The reviewed result remains a semantic consequence of the common
machine candidate; implementing it awaits the broader runtime path.

## Alternating check: selected nested-capture preservation

After the user selected preservation of an already-derived outer callback
capture through a nested concrete receiver, I rechecked the exact implementation
surfaces that rule would cross. Syntax `HirExpr::Apply` remains an associated
syntax shape only; `ResolvedExpr` has no application/call, Force, request,
handler, or resumption cases. `Collector::emit_lambda` still emits recipes only
for parameter identity, integer, and resolved-name bodies. Closed effect views
still expose only `Bottom` / `Empty`, and the backend-neutral core plus VM/native
entrypoints have no execution representation to carry origin, `K,D`, or active
handler identity across the complete `CallView`.

This confirms a **large architecture change**, not a bounded implementation
slice: the preservation theorem needs a resolved call/value relation, symbolic
effect-family carrier and lifecycle transport, and runtime request/handler/
resumption semantics. The source relation and its soundness/principality proof
are not closed, and the user decision is semantic rather than implementation
approval. Defer compiler changes. Continue the source proof; after its next
settled semantic gate, repeat the feasibility audit against the concrete
carrier and transition rules then available. This record update adds no test or
build evidence.

## Targeted alternating check: per-request composition carrier

After closing the conditional `CallView` composition lemma, I checked for a
current implementation carrier matching its exact joint state: source call
origin per request, symbolic `K,D` and shared-binder predicates, and
source-witnessed residual/disappearance. The search found only unrelated
solver `TermLineage` (the immutable term-arena allocation lineage), ordinary
effect-row undo records, and F5 endpoint machinery. Resolved HIR still has no
call/request/Force cases; `PositiveEffectView` / `NegativeEffectView` remain
`Bottom` / `Empty`; `yu-core` and both backend library roots are documentation
boundaries. No type or runtime structure can host the conditional carrier
today.

This agrees with the prior large-architecture classification, but the proof
did not settle which source rules generate callback versus captured-thunk
origins. Thus it does not justify a Rust prototype: such a model would have to
invent the still-unproved source transition. Keep compiler code unchanged.
Next derive the local ownership/Force premises from the ordinary source
relation; once those premises and their independent review close, audit whether
a bounded isolated Rust characterization maps to the actual successor carrier.
No tests, builds, or measurements were run.

## Follow-up proof / feasibility check: event-scoped Force incidence

An adversarial lemma review found that `Capture(origin,h)` is too easy to read
as a reusable grant: one source lineage may expose several dynamic request
events, and a connection justified by one callback execution cannot authorize
another event outside that execution. The reviewed conditional composition
statement now scopes incidence to the current request occurrence, exact
callback invocation/argument contract, and handler activation. `Force`
transports inherited lineage and joint typed predicates; it may create a fresh
event identity, whose capture connection needs its own source witness. Dispatch
is conditional on event-specific `Visible`, matching, and ordered search
actually selecting that handler. A/B differ only in whether the exact
contracted-Force rule may add such a connection; no `iff` or absence claim is
licensed without an exhaustive rule set. Compiler-referee review also required
retaining only requests actually exposed on a represented Force derivation and
preserving `K,D` for dependent surviving views rather than freezing event
incidence literally.

The code check inspected current `ResolvedExpr`, effect views, solver forms,
and crate layout. `ResolvedExpr` still consists of `Lambda`, `Integer`, `Name`,
and `Error`; effect views remain closed `Bottom`/`Empty`, and matching
`Force`/handler/request forms occur only in syntax tests or F5 resource-probe
names, not in the source/runtime path. The newly identified incidence scope
therefore has no event/callback/activation carrier to extend. Both A and B
remain unimplementable as a bounded compiler slice until the successor source
relation and complete effect interface are established. No code or tests were
changed or run.

## Follow-up proof / feasibility check: finite event quotient

The first bounded-event sketch was challenged with recursive same-site
handlers, retained old continuations, and repeated Force. A fixed number of
tracked event references is not sound if overflow means only “these tracked
references may be equal or distinct”: it must represent arbitrarily many
omitted live activations/events, and liveness must include captured values,
latent thunks, stores, and saved continuations. Stack summaries must also
retain repeated frame multiplicity and every resume restoration possibility.
If those correlations are lost, their concretization must include both
eligible and ineligible cases so it cannot certify subtraction.

The proposed finite provenance carrier now has a stricter mathematical target.
For a fixed finite source/interface and representation budget, define a total
deterministic canonicalization `π : ConcreteConfigurations → S_W`, with finite
`S_W`, and let each abstract record denote exactly one fiber of `π`. The fibers
partition the concrete configurations, including unbounded overflow fibers.
Then `α(X) = {π(c) | c ∈ X}` and `γ(B) = π⁻¹(B)` form an adjunction. Summary
coordinates live inside a fiber; they are not overlapping partial records that
each independently denote all compatible configurations. This corrects the
earlier overlapping-record adjunction claim. It remains to define `π` and
prove the required Force/store/unwind/resume/handler coverage.

The exact best collecting transfer over this partition has a least fixed point
in the finite powerset domain, but its computability is not established. A
computable conservative transfer with top fallback can be least for its own
transformer only; that does not establish the least concretely closed
presentation, whole typing/SCC principality, or Oracle final-acceptance parity.
The provenance quotient also does not bound assignment-indexed symbolic
`K,D`; those constraints must remain coupled through the separate type
relation and all scheme lifecycle operations. An architect proposed the
partition quotient. Independent compiler-referee review confirmed the
corrected adjunction but found that `π` is not yet defined on all concrete
states: unbounded live references, recursive frames, dormant stores, and saved
continuations need a deterministic overflow fiber that covers every successor
and re-entry relationship. Stack exit alone cannot release an identity.
This is not a proved finite solver.

The implementation recheck found the same architecture boundary: resolved
expressions still have only `Lambda`, `Integer`, `Name`, and `Error`, and no
runtime Force/handler/continuation state exists to exercise `π` or its transfer.
Thus the new step is theoretical; no Rust prototype, tests, or builds were run.

### Relation to the existing may-origin carrier

The event references belong inside the existing request/continuation relation,
not in another independently joined ledger. Current `ReqFact` projects family,
operation, origin site, and may-blockers; the candidate separately describes
bounded lineage and `KontFact`. The reviewed event distinction requires each
offered request to remain paired with its request-event, callback-invocation,
contract-boundary, and candidate-handler references (or one whole unknown
record), together with route and its symbolic fiber. Equality partitions and
scope alternatives must be joined as complete records so a contract from one
recursive invocation cannot attach to a same-site request from another.

The existing stack projection already saturates old-frame multiplicity as
`Zero/One/Many`; its primitive push/pop review does not cover saved snapshots.
The separate `UnknownKont` proposal supplies the needed conservative shape
only if its concretization includes arbitrary old/new identity relations,
captured-store references, forwarded wrapper re-entry, and every raw-resume
suffix. A summary may conservatively add impossible relationships, but it may
not omit one or recycle an identity still reachable from a dormant value or
continuation. Any ambiguity must make universal `Drop` fail. This connects the
new event-scope obligation to existing finite-carrier work rather than
introducing a second provenance model; its transition coverage and symbolic
`K,D` coupling remain unproved.

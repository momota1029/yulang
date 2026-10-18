# R41 Call output formation: native owner map

Status: Luna read-only owner map, revision 1. This maps existing native
ownership to the proposal questions in R41; it does not supply source typing,
semantic meaning, or implementation authority.

Contract: `tasks/agent-loop/sprints/call-output-formation-20261018-r41.md`,
SHA-256 `1ff014a662f02e4c5e6d5fd084da88f7af6fd993b85437a063fb65807ae745f4`.
The proof proposal is still being authored; candidate-only fields below are
provisional questions, not a claim about its final signature.

## Existing exact-q path

The selected occurrence remains q=`loop y`, the Apply in helper's lambda
body. R40's frozen native trace and its fresh review establish this bounded
consumer path:

| Field or lifecycle fact | Existing producer / consumer | Status and limit |
| --- | --- | --- |
| q occurrence, callee/argument, Apply recipe, checking occurrence, result and application effect | `ConstraintBatch::emit_candidate_source`, `candidate_source.rs:1319–1360`; initial positions and scoped occurrence map at `:863–900` | **Existing native source record.** `ApplySourceInput.result` and `application_effect` are separate component positions. This does not introduce a source description declaration. |
| q's active local-loop route and y formal route | `candidate_source.rs:896,925–931` records parameter/formal-name routes; `:1090–1100,1220–1252` handles active initializer and resolved local/parameter Name routes | **Existing native routing.** It preserves source occurrence and registered/formal endpoint routing; it does not merge loop/helper registrations or create `A_q`. |
| Recipe-to-input/result endpoint retention | `candidate_source.rs:1409–1425`; `ApplySourceInput` creation at `:1319–1360` | **Existing native retention.** q's endpoint is retained as `LambdaRecipe.body_value_endpoint` and as the Apply Value result. This is an endpoint identity/recipe fact, not `Desc(C,rho,sort,sigma,Delta)`. |
| `A_q` declaration/reference, owner, class/sort, original scope and ordered dependency telescope | No producer/consumer in the pinned native path; `ApplySourceInput.introduction:None` is present in the Apply case at `candidate_source.rs:1341` | **Not represented / unverified.** `introduction` is the directional-introduction route only; its `None` does not prove absence of an ordinary source Desc. No validating component, rho, sigma or ordered typed Delta is carried here. |
| q-tied request for the complete source Call suppliers | `CandidateSourceCall::pending_construction` and `PendingCallConstruction::suppliers`, `candidate_call.rs:380–427` | **Existing request only.** It asks for original Call, whole-carrier, receiver/result/future suppliers. The request list does not construct the source formation judgment or authenticate Q's arms. |
| Negative Function demand and separate q Value Result | `InferenceSession::admit_candidate_fact`, `shadow_apply.rs:1763–1895`; `NativeInterface` construction around `:1862` | **Existing native demand.** `NativeInterface.demand` stores the negative Function demand; `.result` stores q's negative Value endpoint. Invocation and application effects are distinct. No source output-description record or returned-provider projection follows. |
| Typed Function Result comparison | `lib.rs:12655–12705` | **Existing native child.** The fourth Function child is the covariant Value Result comparison. It remains a structural comparison of typed endpoints. |
| Preserve admission and dependency retention | `lib.rs:12807–12828`; `candidate_context.rs:3375–3440` | **Existing native owner.** FunctionPort Result is admitted with Preserve, retains parent sources and `Dependency::FunctionPort`, then enqueues the child. |
| Child consumption | `lib.rs:12354–12436`; source provenance seeding in `candidate_context.rs:3246–3320` | **Existing native processing.** Transport/Context/Dispatch process the enqueued relation with q's occurrence/source provenance. This does not create a complete Call typing rule. |
| Helper body result endpoint | `candidate_source.rs:1418–1425`; `lib.rs:11342–11361,11450` | **Existing body endpoint use.** The recipe endpoint is read as helper Function body result. It is not identified with q's complete invocation return/provider/future tuple. |
| Endpoint rewrite/copy during extrusion | `lib.rs:12588–12622`; `candidate_context.rs:3351–3372`; memo at `lib.rs:13052–13070` | **Existing copy handling.** Demand root/dependencies are carried to retained copies. Raw endpoint identity is not claimed across extrusion. |

## Candidate fields versus existing representation

| Potential proposal field | Native owner map |
| --- | --- |
| Fresh output ValueDescription variable and its declaration origin | **Proposed / not represented.** Native Apply allocates a Value component position but no ordinary inference introduction `rho`. A component ordinal is not a source binder. |
| Original source context and ordered typed dependency inclusion | **Proposed / not represented.** Native occurrence scopes, components, levels and retained dependencies do not encode the original type telescope or binder-before-use proof. No native level is a source scope. |
| Return/provider/current-world and dependent future fields in complete `Q_q` | **Source contract exists; this native Apply path has no proved tuple correspondence.** The Call definition/IF records are the source authority. `PendingCallConstruction::suppliers` requests some inputs but does not type or construct all arm fields. |
| Structural, callee-pending, receiver-pending, W/Z and future-arm schemas | **Source contract obligations; native correspondence unverified.** No finite native arm inventory or solver row is used here as a replacement for the original independently quantified source alternatives. |
| Relation from a proposed source Desc to Apply Value Result and complete Call fields | Native result port is retained and structurally consumed as above; the typed source declaration/context square and complete-tuple commutation are **unverified**. |

The candidate's order of formation must come from its source proposal. This map
does not certify that the proposed early output binder is in scope, that its
dependencies are complete, or that erasure preserves accepted source
behavior. In particular, the native Result consumer cannot resolve whether
`A_q` belongs before or after any original Call arm binder.

## Parent, authority, and resource receipt

The map establishes only existing native source retention and structural
Result consumption at q. It supplies no new source rule, semantic adoption,
complete source/native correspondence, CopyScope result, Generalize result,
both-frame transport, or parent theorem premise. The unchanged parent remains
**OPEN, 0 → 0**. No expected-output change or code slice is authorized;
`NO_SAFE_CODE_SLICE` continues for unknown-author dirty Rust inputs.

Checks: static inspection of exact R40-pinned Rust and source-contract paths;
no tests, Cargo, build, CLI, runtime or Git mutation. This Luna lane uses its
600-second grant in full; CPU/RSS and active duration were not metered. Exact
output paths are this note and its assigned R41 handoff. No descendants,
scratch files or generated outputs. Writes stop after the handoff hash is
recorded.

# Source-qualified Entry/Exec/Return plan import contract

Date: 2026-10-17  
Status: Draft, unapplied implementation-readiness contract; the representation and API below are candidate architecture choices, not selected architecture, semantic adoption or compiler-code lease.  
Sprint: `receive-source-derivation-and-plan-bridge-20261017`; implementation lane under contract revision 6.  
Parent: type inference/executor with proofs remains OPEN.

## 1. Purpose and boundary

This contract names the current source-to-runtime seam for the original
two-Call component:

```text
receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit)
alpha+ = ([ctrl]Unit) -> [ctrl]Int
```

It describes how a *future independently source-qualified plan* could be
joined to the playground's existing lowered program and consumed. It does not
claim current `CandidateInference` or HIR supplies such a plan. The separate
plan input and immutable plan arena below are candidate architecture choices;
they are not selected. This Draft does not adopt new receiving semantics,
restrict source admission, edit compiler code, or authorize production cutover.

The source theorem needed to provide original `T` remains OPEN: the first Call
needs an independently satisfying punctured caller context (including the
second-Call obligation) at the original shared indices; the related native
route lacks one anchored full MODEL. A reviewed plan importer cannot fill
these premises.

## 2. Frozen current ownership and the missing field producers

Current source hashes at baseline `6dbb6ad2511b182c1761ecea73f25640eee68899`:

| File | SHA-256 | Existing owner behavior |
| --- | --- | --- |
| `tools/inference-playground/src/lib.rs` | `b65cfd7200e459c9448438ec979ffeb9eddb35c282600349cebe7ddf3b759bbb` | `prepare` returns `(Arc<HirModule>, CandidateInference)`; `execute` binds the candidate to `_candidate` and calls `RuntimeProgram::from_hir(hir, RuntimeEvidence::default())`. |
| `tools/inference-playground/src/runtime/program.rs` | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` | `RuntimeEvidence` contains only occurrence-indexed `name_consumption`. `from_hir` walks source items/local source once, joins expressions through `LocalSourceIndex → Label`, and lowers Lambda to parameter, role, optional `RootCompSchema`, body; Apply stores callee/argument labels. No typed `T` or complete plan is imported. |
| `tools/inference-playground/src/runtime/receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` | `RootCompSchema::from_parameter` accepts an original Comp formal with Unit/Int/Bool/Str, same source root and annotation owner. The selected Value(Function) formal has no matching complete-call schema here. `Receiving` currently stores value views, images, boundaries and receipts. |
| `tools/inference-playground/src/runtime/machine.rs` | `b8f15e4617a9d66940183c7327499ff8a2beb1e9cae2abb997137fc1ca464b82` | `Instruction::Lambda` makes a closure with role/schema/body/environment. `Frame::Callee` makes the delayed argument and selects the actual executable. A Value closure pushes `ValueEntry` then runs the delay; a Comp closure enters its current root schema before binding. `ReceiverReturn` returns the actual value/view; it does not combine a consumed callable's Return recipe. `Frame::Local` installs a completed initializer at its actual local binder. The final body expression returns through the enclosing source body/root. Operation results have a separate post-native `OperationResultConsumer`. |
| `tools/inference-playground/src/runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` | Saved templates retain Bind/Owner/Handler frames and an `ExecutionView`; no callable Entry/Exec/Return recipe exists in a saved frame. The selected simple two-Call plan does not authorize a general continuation redesign. |

The source constructor and reviewed callable-view notes name the intended
fields, but do not supply an implementation producer. The field frontier is:

| Plan field | Current producer status | Current consumer seam |
| --- | --- | --- |
| Original root, occurrence, parameter/binder, local expression, labels | **Produced** by HIR local source and `from_hir` indexing. | `Instruction`, `SourceSite`, `LocalBinding`, `Frame::Local`. |
| Syntax-derived Value/Comp parameter role | **Produced**, but only role, not a typed profile. | `Instruction::Lambda`, `ExecutableValue::Closure`. |
| Comp Unit/Int/Bool/Str `RootCompSchema` | **Produced** for the existing narrow RootComp path. | `Frame::Callee`, Comp entry, `Receiving::enter/receipt`. |
| Name observe/execute decision | **Supplied** through `RuntimeEvidence`; there is no importer for typed callable plans. | `Instruction::Name`, `consume`. |
| Independently valid source `T` and its actual provider/profile/interface certificate | **Missing** from `prepare`/`CandidateInference` at this seam; raw annotation/HIR and candidate solve are not substitutes. | Required before source-plan formation can be asserted. |
| Complete-call `EntryPlan` and actual future-input interfaces for Value(Function) | **Missing**. | Lambda Value entry currently calls `execute(delay)` before `ValueEntry` binds the formal. |
| Per-Apply `ExecPlan` with actual provider, complete-call delimiter, designated consumer | **Missing**. | `Frame::Callee` selects closures/continuations/operations by runtime executable kind. |
| Two-input `ReturnPlan` with original `mu/rho`, tags and result destination | **Missing**. | `ReceiverReturn`, `Frame::Local`, `Frame::RootCompReturn`, body Return and operation consumer. |

## 3. Candidate import interface and source joins

If a later reviewed exporter obtains original `T`, the minimal conceptual seam
is a separate optional parameter to the importer, not an overloaded
`RuntimeEvidence` field:

```text
from_hir_and_source_plan(hir, name_evidence, plan(T)) -> RuntimeProgram
```

The signature is an explanatory contract, not an API selection. It makes the
provenance dependency visible. It must not accept a manually built plan whose
only support is a printed annotation or a satisfiable native candidate.
`CandidateInference` remains a distinct type unless a future reviewed source
export theorem and implementation establish that it owns `T`.

For this selected component, every plan reference must join to the exact
original source owner **and source instance**. Retain, do not reconstruct, the
original instance identity, scope path and shared substitution `xi=(nu,K,D)`
at every dependent node. A source root or occurrence ID alone is insufficient:
the same syntax can be typed under distinct instances, scopes or symbolic
dependencies.

| Node | Required source join | Lowered consumer |
| --- | --- | --- |
| Entry | `SourceRootId`, Lambda occurrence, formal `HirParameterId`, local source parameter, annotation owner/occurrence, role, original slot, original instance identity, scope path and shared `xi=(nu,K,D)` references. | Lambda instruction/closure plus actual Value-entry boundary installation before its designated Force. |
| Execution | Apply occurrence, exact callee and whole-argument `LocalSourceIndex`, actual source provider/interface, complete-call port, designated result consumer, and the same instance/scope/`xi` references. | Apply instruction → `Frame::Callee` → closure/operation consumer path. |
| Return | Original dependent Return binder, same actual return/world, tagged returned packet `W_z`, consumed packet `V_c`, source maps `mu_z/rho_c`, original destination binder, and original instance/scope/`xi`. | `ReceiverReturn` plus the selected result/bind destination (`b_g` for c1; Lambda body-result destination for c2). |
| Future input | Original callee/interface input, complete dependent input interface, shared substitution, and actual later provider entry/annotation identity, instantiated only at that actual entry. | Later actual entry; never the earlier `receive` entry. |

Validation is source identity validation, not semantic proof. Before a
`RuntimeProgram` is made visible, reject a missing root/node, a foreign source
root, an occurrence/parameter/binder/annotation mismatch, a different
instance/scope/substitution at any node, a wrong role or slot, a Return
destination mismatch, duplicate conflicting node definitions, an unregistered
graph cycle, or a plan node not consumed by its matching source constructor.
Multiple references to the *same* registered node remain permitted for real
source sharing/recursion. No scope, instance, substitution, profile or mapping
may be reconstructed from endpoint equality. No field may be inferred from a
runtime value tag, selected definition name, solved support, or a successful
matcher.

## 4. Lifetime, storage and cost contract

- The immutable plan has the same lifetime as its source `RuntimeProgram` and
  its owning `Arc<HirModule>`. `Machine` already retains the program. A frame
  stores a validated plan-node index/reference, not an independently cloned
  plan graph.
- Allocate/index each original derivation/source constructor node once. Build
  graph edges by reference; do not unfold recursive definitions or duplicate
  a Return recipe per runtime execution. Active invocations may retain the
  relevant node index, original receiver/provider handles and actual return
  state only.
- Time and additional index storage are linear in exported plan nodes/edges,
  excluding runtime executions. Plan construction/import adds no scan of all
  effect families and performs no solver queries.
- No new arbitrary source-size cap is selected here. A future implementation
  must use checked node/edge counts and fallible reservation for plan-owned
  vectors/maps, account allocations to the RuntimeProgram lifetime, and report
  resource exhaustion before publishing a partial plan/program. Existing
  runtime step budget governs execution work; it is not a substitute for plan
  allocation accounting. A concrete budget dimension/limit belongs to the
  owning resource policy before code is leased.
- Dropping the final program/machine owner releases the plan arena and indexes
  together. Continuation capture may retain recipe indices only if an actual
  source derivation for that continuation exports and validates those recipes;
  the current two-Call contract does not grant that extension.

This keeps the proposed representation proportional to the compiler's existing
source graph. It does not impose capacity rollback after a failed private
attempt; it requires that no partial program or successful result becomes
observable.

## 5. Failure and execution boundary

Missing source `T` and invalid plan joins are distinct from source type errors.
An importer attempted without its required plan must return a bounded
`RuntimeUnavailable` result before the machine starts. It must not fabricate a
profile, reinterpret HIR shape, or silently route through the plan-aware path
without the complete view. The current playground path remains as-is until an
approved producer/importer is integrated; this document does not change the
existing tool's admission or output behavior.

Construct the program, indexes and plan privately. If source validation,
fallible allocation or plan-erasure checks fail, drop the private attempt and
publish no program/result. A successful constructor must establish that each
plan node corresponds to exactly its source event. Runtime checks then consume
that node at the owning event:

1. **Entry:** install the original current-carrier and callable result
   introductions at their distinct source ports before the actual Value
   argument Force/rebind; do not create a second boundary at local `g`.
2. **Execution:** preserve the actual callee view and complete invocation
   through the original provider entry, body, native return where present,
   and declared result consumer.
3. **Return:** at the same actual Return/world apply the original `mu_z` and
   `rho_c` maps to their separate tagged packets. `c_1` binds at `b_g`; `c_2`
   returns through the body-result path. A pending request has no completed
   Return packet.
4. **Future input:** materialize its introduction only at the actual later
   provider entry; preserve actual old antecedents without copying a
   hypothetical earlier receiver onto that input.

The contract identifies missing enforcement in current `ValueEntry`,
`ReceiverReturn` and `RootCompReturn` paths. It does not authorize editing them
before the producer and source semantics are established and adopted.

## 6. Required review and code gate

This Draft needs independent architecture review of source-plan identity,
program lifetime, resource accounting and consumer ordering, plus independent
spec review that these obligations preserve the selected source semantics and
do not narrow source admission. Review is of this importer contract only; it
does not establish the missing source `T` or approve implementation. The
separate plan input, immutable arena and frame references remain candidate
architecture choices until a later gate explicitly selects them.

Before any compiler code lease, the primary must have:

1. a source producer/exporter that derives all consumed fields from original
   source rules or a reviewed/properly adopted candidate bridge;
2. accepted meanings for Value(Function) entry, complete call and tagged Return
   actions, with original caller/provider premises retained;
3. a source-applicable erasure/simulation argument for this exact fragment;
4. an explicit implementation packet naming only the source/runtime owners
   actually ready and the cleanup/rollback boundary for a reversible
   playground slice;
5. focused verification obligations for source identity mismatches, ordering,
   both Return destinations, request/resumption boundary, and no partial
   publication. Verification is deferred until code authority and user asks or
   sprint contract explicitly grants it.

Until then, this artifact is an unapplied importer contract. The full inference,
executor, source/native, soundness, principality and production gates remain
OPEN.

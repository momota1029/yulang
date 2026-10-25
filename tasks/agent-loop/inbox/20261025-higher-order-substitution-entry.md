# Frozen assignment handoff

Sprint-ID: LEAN-HIGHER-ORDER-SUBSTITUTION-ENTRY-20261025/r1.
Contract: `tasks/agent-loop/sprints/higher-order-substitution-entry-20261025-r1.md` SHA-256 `b8acedd01e960b4198bacd09f4420b394613279538d3c0e5a2d94c45114a6dbc`.
Assignment-ID: higher-order-substitution-entry-astra-r1; handoff revision 1.
Baseline: `98118c2933694a03fcbf443a4cd638e350f76394`.
Author: `/root/higher_order_substitution_entry_astra_r1`, sole author of these three modules and this handoff. No descendants/coauthors in these bytes. Primary owns the independent source-map companion and any later repairs.
Requested model/effort: gpt-6-astra/medium. Observed model/effort: UNKNOWN/UNKNOWN.
Runtime launch receipt: current.json records actual spawn acknowledgment at 2026-10-25T06:27:57.178668+00:00. Author freeze/write-stop: 2026-10-25T06:30:45.835144+00:00. Elapsed to freeze 168.656s / 300s grant. No running process or descendant; no background work.
Outcome class: CANDIDATE constructive Lean proofs and typed research constructions; elaboration and independent review NOT_RUN by author. No reviewed theorem or production authority claimed.

Original parents: HO-SUBSTITUTION-1 / RESPONSE-ENCODING-1 / ENV-CALLABLE-1 under frozen contract. All accepted HigherOrder.Value/Comp/Adapter constructors, arbitrary contexts, successful-lookup-preserving renamings, typed substitutions, arbitrary finite capture layouts and represented current stores, arbitrary higher-order argument/result types. All-source Call/Force/inference A/B and independent F1/FK1 remain unchanged and OPEN.

Parent application:
- `renameValue_typed`, `renameComp_typed`, `renameAdapter_typed` quantify over successful lookup facts only; unused source indices impose no target-none requirement. `up_typed` supplies binder cases.
- `substValue_typed`, `substComp_typed`, `substAdapter_typed` use structural mutual traversal and `lift_typed`. Nested lambda/body, bind, both union branches, request continuation and adapter input are covered. Lambda consumer stays outside lambda parameter binder. Type/op/receipt/path/view metadata is unchanged. `substitute_top` is consumed by computation entry and adapter application.
- Environment finite `realize` aborts on absent reads. Its `Captured`, `captured_index`, `successful_read_typed`, `realized_substitution_typed` feed `close_body`, `close_bound_body`, and `close_adapter`. The filler is irrelevant at every typed layout index.
- `fresh_read`, `fresh_realize`, and `fresh_cells` CONSTRUCT the current-cell premise using Store.push; `fresh_function_closes` supplies these from old FunctionTyped via embedFunction_typed and closes any typed new body. `fresh_function_return` and `fresh_function_argument` consume that construction. This is a formal fresh address reference, never an identification with native ModuleDef. `fresh_lexical_read` additionally connects an actual appended lexical binder to the fresh read.
- `sourceApply_typed` binds the callee and delays the shifted argument; `sourceApply_argument_shift` distinguishes variable 0 from the callee binder.
- Value entry force/binds; Computation entry substitutes the unforced carrier. consumeResult runs the declared result adapter body after the body; wrap delays force/input adaptation before inner dynamicCall and then applies the output adapter. LambdaEntryPlan and WrapEntryPlan retain complete adapters and receipt metadata. `captureEntryPlan` closes ambient body and consumer with their different binder depths. `captured_value_plan_typed` and `captured_computation_plan_typed` apply successful actual finite capture to both entry modes.

Limits and exact owners:
- These typed computation projections do not establish new raw operational semantics, full execution, progress/preservation, receipt generation, native owner/dispatch/template adequacy, or permission to erase metadata.
- Native `substitute_environment` changes dictionary dispatch, not syntactic value substitution (primary source companion evidence). There is no native ExecutableValue::Wrap constructor. No operational equivalence is asserted.
- ENV-LAYOUT-1 remains at source Lambda/Name/Apply lowering and machine.rs Instruction::Lambda/lookup/extend; arbitrary native closure/body/cell encoding and recursive graphs remain ENV-CELL-VALUE-1 / ENV-GRAPH-1. Saved/caller environment and ValueEntry/Callee/Computation correspondence, receiving.rs lambda schemas, defaults/records/unit, dispatch/receipt consumers remain owned by Luna's source/native intake. Full Call/Force/inference parents remain OPEN.
- Generic successful current reads plus typed cell premise is still conditional for arbitrary stores; the fresh callable witness discharges that premise for a constructed store only. It is not a source-layout theorem.

Reuse/rejection:
Reuse Original.up as the type-independent binder helper; reuse the accepted finite capture proof construction from CallEnvironmentRealization, adapted structurally to all higher-order values. Reuse existing generic Store.push/current and structural embedFunction_typed. Do not infer new callable readback from primitive readback. No false untyped old/new substitution commuting claim: old original wrappers protect syntax while embedding exposes it. Failed old CallEntryTyping is not used; no withdrawn inference bypass or weakened source domain.

Checks/resources: file inspection and SHA-256 pin comparison only; all 69 contract-pinned dependencies match: True. Lean/build/tests/native checks NOT_RUN; zero proof-check invocations by author. No Git, production edits, central records, manifests/config, external contacts, new dependencies or scratch paths. Primary owns bounded elaboration/axiom inspection and fresh independent review. No producer certification.

Mutual TODO HOSE-CHECK-1 (Luna): elaborate all three modules, inspect public signatures/axioms and exact binder/capture/entry distinguishing equations, then fresh independent review. Falsifiers: extra lifting of lambda consumer; missing branch/request lift; argument captured by callee binder; forcing Computation entry; reversed wrap adapters; assumed fresh CellsTyped rather than derived; lost metadata; untyped original commuting statement.
Mutual TODO HOSE-NATIVE-1 (Luna/source intake): original native closure layout/cell/graph/dispatch and schema correspondence remain. Inputs are actual source producer/consumer definitions; output must exhibit the emitted layout/body/current-value relation or exact counterexample. Matching typed endpoints or formal assumed transitions is insufficient. NO_SAFE_CODE_SLICE inherited from contract; no production TODO is authorized here.

Next in-scope step: primary acknowledges this frozen handoff and takes stopped module leases for bounded verification/repair; independent review follows. Author assignment ends at this freeze; no waiting worker or continuing process is claimed.

Artifacts (all new paths; exclusive research leases):
- `notes/theory/lean/YulangClosure/HigherOrderSubstitution.lean` SHA-256 `595fd6da855ef3065ef8703e160fe9c7750ad6d692fe80a87437379bc37502fb`
- `notes/theory/lean/YulangClosure/HigherOrderEnvironment.lean` SHA-256 `5721419f87b9bbd1e91db7de68b9df18b62604f1fba3bdeac4ec92d36d9e0503`
- `notes/theory/lean/YulangClosure/HigherOrderEntry.lean` SHA-256 `86cea4087f48de78c3a57a5779bdd1f4f061daaef700ccc4589cb74320b39087`
- `tasks/agent-loop/inbox/20261025-higher-order-substitution-entry.md` (this frozen handoff; hash transmitted out of band).

Direct dependency hashes (full transitive pins remain in frozen contract):
- `notes/theory/lean/YulangClosure/HigherOrderSyntax.lean` SHA-256 `ea727d33692bdcbe6b40245b960d01225b556b5334ffab649eea2699930d5972`
- `notes/theory/lean/YulangClosure/HigherOrderEmbedding.lean` SHA-256 `2b773edf831d04cd4319e1fb980865dff0fb9a38f7d64b21f3d228ea2a0e1457`
- `notes/theory/lean/YulangClosure/CoreSubstitution.lean` SHA-256 `ae1dfd4947d9e87c05dfa893b93067175d860ed3b5da000d61257d7789208b55`
- `notes/theory/lean/YulangClosure/NativeClosureEnvironment.lean` SHA-256 `39aa5cefa078dd423e54f0d9790f9a48e136326742e01f65149f317c907be957`
- `notes/theory/lean/YulangClosure/CallEnvironmentRealization.lean` SHA-256 `8b9e4c38224f103557c5f6a036c6d4d06ba7799264947f4843fa7029195f66b6`

Writer-stop: STOPPED; writes cease with this handoff. Descendants NONE; processes NONE; scratch paths NONE. Pending primary verification/review/integration.

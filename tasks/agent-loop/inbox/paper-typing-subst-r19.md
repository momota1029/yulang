# R19 frozen proof handoff — revision 1

Sprint `FULL-PAPER-TYPE-SUBSTITUTION-20261025/r19`, contract r1 SHA-256 `3f0448e72500adab70e0fa0890aee0c5641032b77dfedf6714bd270d95c6fc74`. Baseline `c5d41edcbd5689f0c4365a0b5330b709fed422ee`; detached worktree `/tmp/yulang-r19-wrap`. The contract was read from its exact committed primary-checkout path. Primary active receipt commit `36000bf2e` cleared invocation1 after all6 input hashes matched. Actual worker `/root/r17_forall`; requested registered `lean_prover`; observed model/effort UNKNOWN. Runtime-exposed shared session `01a172ef-fec1-72e3-bd47-bc4d7f51d6aa`, thread `01a1736a-fc42-7ab1-bc93-ddab8b55fa6d`. This leaf is sole author, with no descendants.

Outcome: constructed and kernel-accepted candidate proof for represented wrap introduction/inversion, direct wrapped Call and arbitrary simultaneous substitution transport across all6 judgments. Independent review and primary final checks PENDING. No self-certification, semantic adoption or parent/production closure.

## Original claim, source mapping and precise declarations

Original parent remains full-paper simultaneous type substitution at `docs/yulang-operational-type-safety-ja.tex:953–977`, within the user's original full inference/executor goal. Source hash `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`. Paper value/computation syntax150–177 includes wrap(f,a,r); rule224 fixes all3 typing premises; Call rule228 consumes the callable and an outer-input thunk. The existing corrected-core value/continuation account §2 V1 and §5 V5(4) is relevant correspondence context, not replacement semantic authority. Original whole-language parent `docs/yulang-whole-proof-closure-ja.md` §1 remains open.

All names below have prefix `YulangClosure.PaperTypes.`:

- New constructor `PaperValueTyped.wrap`: f:callable A B under Γ, a:A under A'::Γ, r:B' under B::Γ; conclusion wrap(f,a,r):callable A' B'. D and Xi are identical across all premises. The exact printed constructor type is retained in invocation2.
- New theorem `PaperValueTyped.wrapInversion`: for arbitrary ty and a derivation typing the actual raw wrap(f,a,r), recovers existential A/B/A'/B', ty=callable A' B', and all3 original typing premises under their exact shared contexts. No typing premise is assumed in place of inversion.
- New theorem `PaperComputationTyped.callWrapped`: from the3 paper wrap premises and thunk:thunk A' under the same Γ, derives Call(wrap(f,a,r),thunk):B' using the existing Call constructor. It does not consume thunk A or return inner B.
- Extended theorem `PaperValueTyped.subst_explicit` retains arbitrary `σ : Nat → Ty`, arbitrary D/Xi/Γ, syntax and result. New wrap recursor case applies the same σ to function and both adapters. `mapTypeEnvironment σ (A'::Γ)` becomes `subst σ A' :: mapTypeEnvironment σ Γ`; similarly B::Γ. Existing `.wrap` mapping and syntax are unchanged.
- Audited preserved conclusions: `ValuesTyped.typeTransport`, `ValuesAllTyped.typeTransport`, `RecordPayloadsTyped.typeTransport`, `PaperComputationTyped.typeTransport`, `PaperContinuationTyped.typeTransport`; all quantify over arbitrary σ and retain all respective indices, including distinct continuation response/result.

Complete fully qualified theorem types and full axiom reports are below; this description does not replace them. Every delivered theorem is a theorem declaration checked by the bundled helper.

## Source scope and parent application

All prior36 constructors and premises are preserved; only wrap is added, making37. A direct source comparison removed the single new constructor block and recovered the original Syntax bytes exactly. Removing the new recursor branch and the2 new theorem blocks recovers the old TypingSubstitution token sequence. No existing syntax/mapping, binder rule, declaration/operation instantiation, record premises, source quantifier or shared witness changed.

The new constructor applies the manuscript224 premises directly. Existing Call then consumes it with the manuscript228 thunk premise; arbitrary-σ preservation now covers this exact represented rule. This discharges only the R19 represented wrap premise. Full parent remains OPEN: R18 variant typeArguments correspondence is still primary-owned and unresolved; nominal, switch and other missing typing rules, recursive graph guards and full inference/executor/source-native correspondence retain their owners. The primary owns subsequent exact rule-coverage and source-proof packets. No proposition definition or LocalLaws parameter is promoted to a concrete source instance.

Mapping scope is paper raw wrap constructor -> exact extrinsic introduction -> same-σ syntax/context transport -> existing Call typing consumer. No constraint generator, execution-step relation, runtime/native realization or Rust correspondence was constructed or tested. No implementation/production lane was admitted.

## Actual checks, axioms, resources and writes

Invocation1: native installed Lake path `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`, focused Syntax/TypingSubstitution build including fresh dependency build, exit0,23.970148s.
Invocation2: same native Lake `env lean -j1 -M1024 .lake/R19Audit.lean`, exit0,1.993374s. Both cwd `/tmp/yulang-r19-wrap/notes/theory/lean`; LEAN_NUM_THREADS=1; project moreLeanArgs also `-j1 -M1024`.

All8 named theorem types and complete axiom lists PASS via bundled `check_lean.py` functions `audit_source` and `validate_audit`, using only the exact leased audit file. Standalone CLI was avoided because it creates an unleased temporary path. Each theorem depends exactly on `[propext, Quot.sound]`; the wrap constructor reports `does not depend on any axioms`. No sorryAx, Classical.choice, project axiom or checker bypass. Source inspection of the complete6-module dependency cone found no sorry/admit/axiom/native_decide/skipKernelTC token matches. There were no Lean failures or repairs to conceal.

Toolchain pin is Lean4.35.0, native path resolved from the previously established installed distribution. No separate version/reconnaissance invocation was run under this contract; no new version receipt is invented. Read lean-toolchain/lakefile/manifest: YulangClosure library, no external packages. Existing versions from earlier packets are not counted as R19 execution. No tests, installation, new dependencies or global-default changes.

Resources: 2 literal serial Lake invocations,25.963522 checker seconds. Worker calls3–6 unused; primary7–8 reserved. No old budget transferred. Active-time telemetry was not instrumented; no fabricated measurement. Work completed within the900-active-second and120-checker-second envelope. Sole authored files are the2 leased modules, exact R19Audit and this handoff; generated `.lake/build` outputs are worktree-local dedicated-cache artifacts. No root import, main-checkout source, compiler/Rust, configuration, tasks/status/contract or Git mutation. No other worker paths, appointments, external contact or children.

STOPPED: both checker subprocess sessions returned exit0, no remaining process or descendant. After this final handoff write, all source/scratch/handoff/cache writes STOPPED. Dedicated cache ownership is released to primary for reserved final checks. Artifact review is pending; this receipt is not independent review or production permission.

Frozen input/artifact SHA-256:
- `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean`: `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`
- `notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean`: `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `notes/theory/lean/YulangClosure/PaperTypeFormation.lean`: `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `notes/theory/lean/YulangClosure/DeclSubst.lean`: `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- `docs/yulang-operational-type-safety-ja.tex`: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`: `2192b5de98b9af217318dd95db93c6fd4b776e93266f62ec7e4e23402166acb3`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`: `6c41d59cf9326b2e94e612b62c02448991979d60658a88a001a4e7143bbfefdc`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperExecutionSyntax.olean`: `e78b9f11560dabc2d779ca3faa7568c66b6b7ae70cd6d036117beaf870fc9e90`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperExecutionBinderLaws.olean`: `2739231c458630d06438594042b063868278bcf1c8d6f91e87ce19248c178ee6`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperExecutionTypingSubstitution.olean`: `2cab9fe04e495ef2c395e0ba565ac0cb9793ebf08059d0242ea2b526a7cf8904`
- `notes/theory/lean/.lake/R19Audit.lean`: `d6f4ea5cb8206784ef0794007adc207331738a2157df7c9def803c60ee4c0263`

Full original command output and exact type/axiom receipts follow unchanged.

---

# R19 construction receipt (unfrozen)

Contract SHA-256 `3f0448e72500adab70e0fa0890aee0c5641032b77dfedf6714bd270d95c6fc74`; baseline `c5d41edcbd5689f0c4365a0b5330b709fed422ee`. All six frozen dependency hashes matched before writing. Primary cleared invocation1 after active receipt commit36000bf2e. Exposed runtime CODEX_SESSION_ID `01a172ef-fec1-72e3-bd47-bc4d7f51d6aa`, CODEX_THREAD_ID `01a1736a-fc42-7ab1-bc93-ddab8b55fa6d`; observed model/effort UNKNOWN. Exact source rule: manuscript224, original substitution953–977.

Invocation1 `['/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', 'build', '+YulangClosure.PaperExecutionSyntax', '+YulangClosure.PaperExecutionTypingSubstitution']`; exit0; elapsed23.970148s; cwd `/tmp/yulang-r19-wrap/notes/theory/lean`
```text
✔ [1/5] Built YulangClosure.PaperTypeSubstitution (3.3s)
✔ [3/7] Built YulangClosure.PaperTypeFormation (8.6s)
✔ [4/7] Built YulangClosure.DeclSubst (250ms)
⚠ [5/7] Built YulangClosure.PaperExecutionSyntax (7.0s)
warning: YulangClosure/PaperExecutionSyntax.lean:179:61: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:180:67: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:181:63: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:185:42: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:188:42: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:236:42: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:244:42: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:250:54: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:255:41: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:266:37: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:270:42: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:279:13: Variable name `hsmall` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hsmall

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:297:65: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:299:55: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:300:43: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:301:70: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:303:16: Variable name `hdefault` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hdefault

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:307:59: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:310:44: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:323:13: Variable name `hsmall` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hsmall

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:326:13: Variable name `hsmall` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hsmall

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:442:42: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: YulangClosure/PaperExecutionSyntax.lean:443:46: Variable name `hmem` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hmem

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [6/7] Built YulangClosure.PaperExecutionBinderLaws (3.6s)
warning: YulangClosure/PaperExecutionBinderLaws.lean:67:12: This simp argument is unused:
  liftSubN

Hint: Omit it from the simp argument list.
  [apply] simp [Nat.add_assoc]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:67:22: This simp argument is unused:
  Nat.add_assoc

Hint: Omit it from the simp argument list.
  [apply] simp [liftSubN]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:201:28: This simp argument is unused:
  mapPaperComputation

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:201:49: This simp argument is unused:
  mapPaperPattern

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:201:66: This simp argument is unused:
  mapConstructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:202:14: This simp argument is unused:
  mapGuardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:202:32: This simp argument is unused:
  mapValueArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:202:45: This simp argument is unused:
  mapOperationArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:202:62: This simp argument is unused:
  mapHandlerPlan

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:202:78: This simp argument is unused:
  mapMapperPlan

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:204:14: This simp argument is unused:
  mapOperationInstance_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:205:47: This simp argument is unused:
  liftSubN_add

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:206:14: This simp argument is unused:
  h_pattern

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:206:25: This simp argument is unused:
  h_constructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_guardedBranch,
    h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq, mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:206:46: This simp argument is unused:
  h_guardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:206:63: This simp argument is unused:
  h_valueArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:207:14: This simp argument is unused:
  h_operationArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:207:30: This simp argument is unused:
  h_handler

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:207:41: This simp argument is unused:
  h_mapper

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:208:14: This simp argument is unused:
  mapPaperComputation_recursive_eq

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:223:45: This simp argument is unused:
  h_computation

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm,
    h_handler, h_mapper]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:223:60: This simp argument is unused:
  h_pattern

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_computation, h_constructorBranch, h_guardedBranch, h_valueArm,
    h_operationArm, h_handler, h_mapper]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:223:71: This simp argument is unused:
  h_constructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_computation, h_pattern, h_guardedBranch, h_valueArm, h_operationArm,
    h_handler, h_mapper]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:224:15: This simp argument is unused:
  h_guardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch, h_valueArm, h_operationArm,
    h_handler, h_mapper]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:224:32: This simp argument is unused:
  h_valueArm

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch, h_guardedBranch,
    h_operationArm, h_handler, h_mapper]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:224:44: This simp argument is unused:
  h_operationArm

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
    h_handler, h_mapper]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:224:60: This simp argument is unused:
  h_handler

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
    h_operationArm, h_mapper]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:224:71: This simp argument is unused:
  h_mapper

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
    h_operationArm, h_handler]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:230:11: This simp argument is unused:
  mapPaperValue

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:230:47: This simp argument is unused:
  mapPaperPattern

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:230:64: This simp argument is unused:
  mapConstructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:231:12: This simp argument is unused:
  mapGuardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:231:30: This simp argument is unused:
  mapValueArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:231:43: This simp argument is unused:
  mapOperationArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:231:60: This simp argument is unused:
  mapHandlerPlan

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:231:76: This simp argument is unused:
  mapMapperPlan

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:232:30: This simp argument is unused:
  mapAdapterMetadata_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:234:45: This simp argument is unused:
  liftSubN_add

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:235:12: This simp argument is unused:
  h_pattern

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:235:23: This simp argument is unused:
  h_constructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_guardedBranch,
    h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq, mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:235:44: This simp argument is unused:
  h_guardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:235:61: This simp argument is unused:
  h_valueArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:236:49: This simp argument is unused:
  mapPaperValue_record_eq

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:252:43: This simp argument is unused:
  h_computation

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm,
    h_handler, h_mapper]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:252:58: This simp argument is unused:
  h_pattern

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_computation, h_constructorBranch, h_guardedBranch, h_valueArm,
    h_operationArm, h_handler, h_mapper]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:253:13: This simp argument is unused:
  h_guardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch, h_valueArm, h_operationArm,
    h_handler, h_mapper]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:253:30: This simp argument is unused:
  h_valueArm

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch, h_guardedBranch,
    h_operationArm, h_handler, h_mapper]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:253:58: This simp argument is unused:
  h_handler

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
    h_operationArm, h_mapper]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:253:69: This simp argument is unused:
  h_mapper

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
    h_operationArm, h_handler]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:259:11: This simp argument is unused:
  mapPaperValue

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:259:26: This simp argument is unused:
  mapPaperComputation

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:259:64: This simp argument is unused:
  mapConstructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:260:12: This simp argument is unused:
  mapGuardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:260:30: This simp argument is unused:
  mapValueArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:260:43: This simp argument is unused:
  mapOperationArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:260:60: This simp argument is unused:
  mapHandlerPlan

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:260:76: This simp argument is unused:
  mapMapperPlan

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:261:30: This simp argument is unused:
  mapAdapterMetadata_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:261:56: This simp argument is unused:
  mapViewMetadata_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:262:12: This simp argument is unused:
  mapOperationInstance_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:263:45: This simp argument is unused:
  liftSubN_add

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:264:23: This simp argument is unused:
  h_constructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_guardedBranch,
    h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq, mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:264:44: This simp argument is unused:
  h_guardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:264:61: This simp argument is unused:
  h_valueArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:265:12: This simp argument is unused:
  h_operationArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:265:28: This simp argument is unused:
  h_handler

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:265:39: This simp argument is unused:
  h_mapper

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:265:49: This simp argument is unused:
  mapPaperValue_record_eq

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:266:12: This simp argument is unused:
  mapPaperComputation_recursive_eq

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:283:11: This simp argument is unused:
  mapPaperValue

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:283:26: This simp argument is unused:
  mapPaperComputation

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:283:47: This simp argument is unused:
  mapPaperPattern

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:284:12: This simp argument is unused:
  mapGuardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:284:30: This simp argument is unused:
  mapValueArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:284:43: This simp argument is unused:
  mapOperationArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:284:60: This simp argument is unused:
  mapHandlerPlan

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:284:76: This simp argument is unused:
  mapMapperPlan

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:285:12: This simp argument is unused:
  mapTypeArguments

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:285:30: This simp argument is unused:
  mapAdapterMetadata_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:285:56: This simp argument is unused:
  mapViewMetadata_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:286:12: This simp argument is unused:
  mapOperationInstance_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:286:40: This simp argument is unused:
  List.attach_map_val

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:286:61: This simp argument is unused:
  List.attach_map

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:287:12: This simp argument is unused:
  List.map_map

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:287:26: This simp argument is unused:
  List.map_inj_left

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:287:45: This simp argument is unused:
  liftSubN_add

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:287:59: This simp argument is unused:
  h_value

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:288:12: This simp argument is unused:
  h_pattern

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:288:23: This simp argument is unused:
  h_constructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_guardedBranch,
    h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq, mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:288:44: This simp argument is unused:
  h_guardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:288:61: This simp argument is unused:
  h_valueArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:289:12: This simp argument is unused:
  h_operationArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:289:28: This simp argument is unused:
  h_handler

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:289:39: This simp argument is unused:
  h_mapper

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:289:49: This simp argument is unused:
  mapPaperValue_record_eq

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:290:12: This simp argument is unused:
  mapPaperComputation_recursive_eq

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:314:13: This simp argument is unused:
  mapPaperValue

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:314:28: This simp argument is unused:
  mapPaperComputation

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:314:49: This simp argument is unused:
  mapPaperPattern

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:314:66: This simp argument is unused:
  mapConstructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:315:32: This simp argument is unused:
  mapValueArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:315:45: This simp argument is unused:
  mapOperationArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:315:62: This simp argument is unused:
  mapHandlerPlan

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:315:78: This simp argument is unused:
  mapMapperPlan

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:316:14: This simp argument is unused:
  mapTypeArguments

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:316:32: This simp argument is unused:
  mapAdapterMetadata_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:316:58: This simp argument is unused:
  mapViewMetadata_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:317:14: This simp argument is unused:
  mapOperationInstance_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:317:42: This simp argument is unused:
  List.attach_map_val

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:317:63: This simp argument is unused:
  List.attach_map

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:318:14: This simp argument is unused:
  List.map_map

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:318:28: This simp argument is unused:
  List.map_inj_left

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:318:47: This simp argument is unused:
  liftSubN_add

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:318:61: This simp argument is unused:
  h_value

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:319:25: This simp argument is unused:
  h_constructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_guardedBranch,
    h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq, mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:319:46: This simp argument is unused:
  h_guardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:319:63: This simp argument is unused:
  h_valueArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:320:14: This simp argument is unused:
  h_operationArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:320:30: This simp argument is unused:
  h_handler

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:320:41: This simp argument is unused:
  h_mapper

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:320:51: This simp argument is unused:
  mapPaperValue_record_eq

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:321:14: This simp argument is unused:
  mapPaperComputation_recursive_eq

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:327:11: This simp argument is unused:
  mapPaperValue

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:327:26: This simp argument is unused:
  mapPaperComputation

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:327:47: This simp argument is unused:
  mapPaperPattern

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:327:64: This simp argument is unused:
  mapConstructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:328:12: This simp argument is unused:
  mapGuardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:328:43: This simp argument is unused:
  mapOperationArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:328:60: This simp argument is unused:
  mapHandlerPlan

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:328:76: This simp argument is unused:
  mapMapperPlan

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:329:12: This simp argument is unused:
  mapTypeArguments

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:329:30: This simp argument is unused:
  mapAdapterMetadata_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:329:56: This simp argument is unused:
  mapViewMetadata_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:330:12: This simp argument is unused:
  mapOperationInstance_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:330:40: This simp argument is unused:
  List.attach_map_val

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:330:61: This simp argument is unused:
  List.attach_map

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:331:12: This simp argument is unused:
  List.map_map

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:331:26: This simp argument is unused:
  List.map_inj_left

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:331:45: This simp argument is unused:
  liftSubN_add

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:331:59: This simp argument is unused:
  h_value

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:331:68: This simp argument is unused:
  h_computation

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:332:12: This simp argument is unused:
  h_pattern

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:332:23: This simp argument is unused:
  h_constructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_guardedBranch,
    h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq, mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:332:61: This simp argument is unused:
  h_valueArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:333:12: This simp argument is unused:
  h_operationArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:333:28: This simp argument is unused:
  h_handler

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:333:39: This simp argument is unused:
  h_mapper

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:333:49: This simp argument is unused:
  mapPaperValue_record_eq

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:334:12: This simp argument is unused:
  mapPaperComputation_recursive_eq

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:358:13: This simp argument is unused:
  mapPaperValue

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:358:28: This simp argument is unused:
  mapPaperComputation

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:358:49: This simp argument is unused:
  mapPaperPattern

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:358:66: This simp argument is unused:
  mapConstructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:359:14: This simp argument is unused:
  mapGuardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:359:32: This simp argument is unused:
  mapValueArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:359:62: This simp argument is unused:
  mapHandlerPlan

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:359:78: This simp argument is unused:
  mapMapperPlan

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:360:14: This simp argument is unused:
  mapTypeArguments

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:360:32: This simp argument is unused:
  mapAdapterMetadata_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:360:58: This simp argument is unused:
  mapViewMetadata_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:361:14: This simp argument is unused:
  mapOperationInstance_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:361:42: This simp argument is unused:
  List.attach_map_val

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:361:63: This simp argument is unused:
  List.attach_map

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:362:14: This simp argument is unused:
  List.map_map

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:362:28: This simp argument is unused:
  List.map_inj_left

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:362:61: This simp argument is unused:
  h_value

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:363:25: This simp argument is unused:
  h_constructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_guardedBranch,
    h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq, mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:363:46: This simp argument is unused:
  h_guardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:363:63: This simp argument is unused:
  h_valueArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:364:14: This simp argument is unused:
  h_operationArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:364:30: This simp argument is unused:
  h_handler

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:364:41: This simp argument is unused:
  h_mapper

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:364:51: This simp argument is unused:
  mapPaperValue_record_eq

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:365:14: This simp argument is unused:
  mapPaperComputation_recursive_eq

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:371:11: This simp argument is unused:
  mapPaperValue

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:371:26: This simp argument is unused:
  mapPaperComputation

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:371:47: This simp argument is unused:
  mapPaperPattern

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:371:64: This simp argument is unused:
  mapConstructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:372:12: This simp argument is unused:
  mapGuardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:372:30: This simp argument is unused:
  mapValueArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:372:43: This simp argument is unused:
  mapOperationArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:372:76: This simp argument is unused:
  mapMapperPlan

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:373:12: This simp argument is unused:
  mapTypeArguments

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:373:30: This simp argument is unused:
  mapAdapterMetadata_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:373:56: This simp argument is unused:
  mapViewMetadata_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:374:12: This simp argument is unused:
  mapOperationInstance_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:375:45: This simp argument is unused:
  liftSubN_add

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:375:59: This simp argument is unused:
  h_value

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:375:68: This simp argument is unused:
  h_computation

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:376:12: This simp argument is unused:
  h_pattern

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:376:23: This simp argument is unused:
  h_constructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_guardedBranch,
    h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq, mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:376:44: This simp argument is unused:
  h_guardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:376:61: This simp argument is unused:
  h_valueArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:377:12: This simp argument is unused:
  h_operationArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:377:28: This simp argument is unused:
  h_handler

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:377:39: This simp argument is unused:
  h_mapper

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:377:49: This simp argument is unused:
  mapPaperValue_record_eq

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:378:12: This simp argument is unused:
  mapPaperComputation_recursive_eq

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:393:34: This simp argument is unused:
  h_value

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_computation, h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
    h_operationArm, h_handler, h_mapper]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:393:43: This simp argument is unused:
  h_computation

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm,
    h_handler, h_mapper]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:393:58: This simp argument is unused:
  h_pattern

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_computation, h_constructorBranch, h_guardedBranch, h_valueArm,
    h_operationArm, h_handler, h_mapper]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:393:69: This simp argument is unused:
  h_constructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_computation, h_pattern, h_guardedBranch, h_valueArm, h_operationArm,
    h_handler, h_mapper]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:394:13: This simp argument is unused:
  h_guardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch, h_valueArm, h_operationArm,
    h_handler, h_mapper]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:394:58: This simp argument is unused:
  h_handler

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
    h_operationArm, h_mapper]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:394:69: This simp argument is unused:
  h_mapper

Hint: Omit it from the simp argument list.
  [apply] simp (disch := omega) [h_value, h_computation, h_pattern, h_constructorBranch, h_guardedBranch, h_valueArm,
    h_operationArm, h_handler]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:400:11: This simp argument is unused:
  mapPaperValue

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:400:26: This simp argument is unused:
  mapPaperComputation

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:400:47: This simp argument is unused:
  mapPaperPattern

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:400:64: This simp argument is unused:
  mapConstructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:401:12: This simp argument is unused:
  mapGuardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:401:30: This simp argument is unused:
  mapValueArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapOperationArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:401:43: This simp argument is unused:
  mapOperationArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapHandlerPlan, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:401:60: This simp argument is unused:
  mapHandlerPlan

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapMapperPlan, mapTypeArguments,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:402:12: This simp argument is unused:
  mapTypeArguments

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:402:30: This simp argument is unused:
  mapAdapterMetadata_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:402:56: This simp argument is unused:
  mapViewMetadata_shift

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapOperationInstance_shift, List.attach_map_val, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:403:40: This simp argument is unused:
  List.attach_map_val

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:403:61: This simp argument is unused:
  List.attach_map

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:404:12: This simp argument is unused:
  List.map_map

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:404:26: This simp argument is unused:
  List.map_inj_left

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, liftSubN_add, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:404:45: This simp argument is unused:
  liftSubN_add

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, h_value, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:404:59: This simp argument is unused:
  h_value

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_computation, h_pattern, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:405:12: This simp argument is unused:
  h_pattern

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_constructorBranch,
    h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:405:23: This simp argument is unused:
  h_constructorBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern, h_guardedBranch,
    h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq, mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:405:44: This simp argument is unused:
  h_guardedBranch

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:405:61: This simp argument is unused:
  h_valueArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:406:12: This simp argument is unused:
  h_operationArm

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_handler, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:406:28: This simp argument is unused:
  h_handler

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_mapper, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:406:39: This simp argument is unused:
  h_mapper

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, mapPaperValue_record_eq,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:406:49: This simp argument is unused:
  mapPaperValue_record_eq

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper,
    mapPaperComputation_recursive_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:407:12: This simp argument is unused:
  mapPaperComputation_recursive_eq

Hint: Omit it from the simp argument list.
  [apply] simp (config := { contextual := true }) (disch := omega) [mapPaperValue, mapPaperComputation, mapPaperPattern,
    mapConstructorBranch, mapGuardedBranch, mapValueArm, mapOperationArm, mapHandlerPlan, mapMapperPlan,
    mapTypeArguments, mapAdapterMetadata_shift, mapViewMetadata_shift, mapOperationInstance_shift, List.attach_map_val,
    List.attach_map, List.map_map, List.map_inj_left, liftSubN_add, h_value, h_computation, h_pattern,
    h_constructorBranch, h_guardedBranch, h_valueArm, h_operationArm, h_handler, h_mapper, mapPaperValue_record_eq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:481:57: This simp argument is unused:
  List.map_map

Hint: Omit it from the simp argument list.
  [apply] simp [OperationDeclaration.substAmbient, liftSubN_add, mapPaperComputation_shift_substitution_commutes]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:481:71: This simp argument is unused:
  mapPaperComputation_shift_substitution_commutes

Hint: Omit it from the simp argument list.
  [apply] simp [OperationDeclaration.substAmbient, liftSubN_add, List.map_map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:487:59: This simp argument is unused:
  mapPaperComputation_shift_substitution_commutes

Hint: Omit it from the simp argument list.
  [apply] simp [mapNominalConstructor, liftSubN_add, List.map_map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: YulangClosure/PaperExecutionBinderLaws.lean:493:59: This simp argument is unused:
  mapPaperComputation_shift_substitution_commutes

Hint: Omit it from the simp argument list.
  [apply] simp [mapPrimitiveSignature, liftSubN_add, List.map_map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
✔ [7/7] Built YulangClosure.PaperExecutionTypingSubstitution (643ms)
Build completed successfully (7 jobs).

```

Invocation2 `['/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', 'env', 'lean', '-j1', '-M1024', '.lake/R19Audit.lean']`; exit0; elapsed1.993374s; cwd `/tmp/yulang-r19-wrap/notes/theory/lean`
```text
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperValueTyped.subst_explicit
YulangClosure.PaperTypes.PaperValueTyped.subst_explicit : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  {declarations : YulangClosure.PaperTypes.DeclarationTable} {graphTypes : YulangClosure.PaperTypes.GraphEnvironment}
  {environment : YulangClosure.PaperTypes.TypeEnvironment} {value : YulangClosure.PaperTypes.Value}
  {ty : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperValueTyped declarations graphTypes environment value ty →
    YulangClosure.PaperTypes.PaperValueTyped (YulangClosure.PaperTypes.mapDeclarationTable σ declarations)
      (YulangClosure.PaperTypes.mapGraphEnvironment σ graphTypes)
      (YulangClosure.PaperTypes.mapTypeEnvironment σ environment) (YulangClosure.PaperTypes.mapPaperValue σ value)
      (YulangClosure.PaperTypes.subst σ ty)
'YulangClosure.PaperTypes.PaperValueTyped.subst_explicit' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperValueTyped.subst_explicit
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.ValuesTyped.typeTransport
YulangClosure.PaperTypes.ValuesTyped.typeTransport : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  {declarations : YulangClosure.PaperTypes.DeclarationTable} {graphTypes : YulangClosure.PaperTypes.GraphEnvironment}
  {environment : YulangClosure.PaperTypes.TypeEnvironment} {values : List YulangClosure.PaperTypes.Value}
  {types : List YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.ValuesTyped declarations graphTypes environment values types →
    YulangClosure.PaperTypes.ValuesTyped (YulangClosure.PaperTypes.mapDeclarationTable σ declarations)
      (YulangClosure.PaperTypes.mapGraphEnvironment σ graphTypes)
      (YulangClosure.PaperTypes.mapTypeEnvironment σ environment)
      (List.map (YulangClosure.PaperTypes.mapPaperValue σ) values) (List.map (YulangClosure.PaperTypes.subst σ) types)
'YulangClosure.PaperTypes.ValuesTyped.typeTransport' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.ValuesTyped.typeTransport
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.ValuesAllTyped.typeTransport
YulangClosure.PaperTypes.ValuesAllTyped.typeTransport : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  {declarations : YulangClosure.PaperTypes.DeclarationTable} {graphTypes : YulangClosure.PaperTypes.GraphEnvironment}
  {environment : YulangClosure.PaperTypes.TypeEnvironment} {values : List YulangClosure.PaperTypes.Value}
  {ty : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.ValuesAllTyped declarations graphTypes environment values ty →
    YulangClosure.PaperTypes.ValuesAllTyped (YulangClosure.PaperTypes.mapDeclarationTable σ declarations)
      (YulangClosure.PaperTypes.mapGraphEnvironment σ graphTypes)
      (YulangClosure.PaperTypes.mapTypeEnvironment σ environment)
      (List.map (YulangClosure.PaperTypes.mapPaperValue σ) values) (YulangClosure.PaperTypes.subst σ ty)
'YulangClosure.PaperTypes.ValuesAllTyped.typeTransport' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.ValuesAllTyped.typeTransport
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport
YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  {declarations : YulangClosure.PaperTypes.DeclarationTable} {graphTypes : YulangClosure.PaperTypes.GraphEnvironment}
  {environment : YulangClosure.PaperTypes.TypeEnvironment}
  {fields : List (YulangClosure.PaperTypes.Label × YulangClosure.PaperTypes.Presence × YulangClosure.PaperTypes.Value)}
  {recordType : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.RecordPayloadsTyped declarations graphTypes environment fields recordType →
    YulangClosure.PaperTypes.RecordPayloadsTyped (YulangClosure.PaperTypes.mapDeclarationTable σ declarations)
      (YulangClosure.PaperTypes.mapGraphEnvironment σ graphTypes)
      (YulangClosure.PaperTypes.mapTypeEnvironment σ environment) (YulangClosure.PaperTypes.mapRecordFields σ fields)
      (YulangClosure.PaperTypes.subst σ recordType)
'YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperComputationTyped.typeTransport
YulangClosure.PaperTypes.PaperComputationTyped.typeTransport : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  {declarations : YulangClosure.PaperTypes.DeclarationTable} {graphTypes : YulangClosure.PaperTypes.GraphEnvironment}
  {environment : YulangClosure.PaperTypes.TypeEnvironment} {computation : YulangClosure.PaperTypes.Computation}
  {ty : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes environment computation ty →
    YulangClosure.PaperTypes.PaperComputationTyped (YulangClosure.PaperTypes.mapDeclarationTable σ declarations)
      (YulangClosure.PaperTypes.mapGraphEnvironment σ graphTypes)
      (YulangClosure.PaperTypes.mapTypeEnvironment σ environment)
      (YulangClosure.PaperTypes.mapPaperComputation σ computation) (YulangClosure.PaperTypes.subst σ ty)
'YulangClosure.PaperTypes.PaperComputationTyped.typeTransport' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperComputationTyped.typeTransport
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport
YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  {declarations : YulangClosure.PaperTypes.DeclarationTable} {graphTypes : YulangClosure.PaperTypes.GraphEnvironment}
  {environment : YulangClosure.PaperTypes.TypeEnvironment} {continuation : YulangClosure.PaperTypes.Value}
  {response result : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperContinuationTyped declarations graphTypes environment continuation response result →
    YulangClosure.PaperTypes.PaperContinuationTyped (YulangClosure.PaperTypes.mapDeclarationTable σ declarations)
      (YulangClosure.PaperTypes.mapGraphEnvironment σ graphTypes)
      (YulangClosure.PaperTypes.mapTypeEnvironment σ environment)
      (YulangClosure.PaperTypes.mapPaperValue σ continuation) (YulangClosure.PaperTypes.subst σ response)
      (YulangClosure.PaperTypes.subst σ result)
'YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperValueTyped.wrapInversion
@YulangClosure.PaperTypes.PaperValueTyped.wrapInversion : ∀ {declarations : YulangClosure.PaperTypes.DeclarationTable}
  {graphTypes : YulangClosure.PaperTypes.GraphEnvironment} {environment : YulangClosure.PaperTypes.TypeEnvironment}
  {function : YulangClosure.PaperTypes.Value} {argumentAdapter resultAdapter : YulangClosure.PaperTypes.Computation}
  {ty : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperValueTyped declarations graphTypes environment
      (function.wrap argumentAdapter resultAdapter) ty →
    ∃ inputType outputType adaptedInputType adaptedOutputType,
      ty = adaptedInputType.callable adaptedOutputType ∧
        YulangClosure.PaperTypes.PaperValueTyped declarations graphTypes environment function
            (inputType.callable outputType) ∧
          YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes (adaptedInputType :: environment)
              argumentAdapter inputType ∧
            YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes (outputType :: environment)
              resultAdapter adaptedOutputType
'YulangClosure.PaperTypes.PaperValueTyped.wrapInversion' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperValueTyped.wrapInversion
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperComputationTyped.callWrapped
@YulangClosure.PaperTypes.PaperComputationTyped.callWrapped : ∀
  {declarations : YulangClosure.PaperTypes.DeclarationTable} {graphTypes : YulangClosure.PaperTypes.GraphEnvironment}
  {environment : YulangClosure.PaperTypes.TypeEnvironment} {function thunk : YulangClosure.PaperTypes.Value}
  {argumentAdapter resultAdapter : YulangClosure.PaperTypes.Computation}
  {inputType outputType adaptedInputType adaptedOutputType : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperValueTyped declarations graphTypes environment function
      (inputType.callable outputType) →
    YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes (adaptedInputType :: environment)
        argumentAdapter inputType →
      YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes (outputType :: environment) resultAdapter
          adaptedOutputType →
        YulangClosure.PaperTypes.PaperValueTyped declarations graphTypes environment thunk adaptedInputType.thunk →
          YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes environment
            (YulangClosure.PaperTypes.Computation.call (function.wrap argumentAdapter resultAdapter) thunk)
            adaptedOutputType
'YulangClosure.PaperTypes.PaperComputationTyped.callWrapped' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperComputationTyped.callWrapped
@YulangClosure.PaperTypes.PaperValueTyped.wrap : ∀ {declarations : YulangClosure.PaperTypes.DeclarationTable}
  {graphTypes : YulangClosure.PaperTypes.GraphEnvironment} {environment : YulangClosure.PaperTypes.TypeEnvironment}
  {function : YulangClosure.PaperTypes.Value} {argumentAdapter resultAdapter : YulangClosure.PaperTypes.Computation}
  {inputType outputType adaptedInputType adaptedOutputType : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperValueTyped declarations graphTypes environment function
      (inputType.callable outputType) →
    YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes (adaptedInputType :: environment)
        argumentAdapter inputType →
      YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes (outputType :: environment) resultAdapter
          adaptedOutputType →
        YulangClosure.PaperTypes.PaperValueTyped declarations graphTypes environment
          (function.wrap argumentAdapter resultAdapter) (adaptedInputType.callable adaptedOutputType)
'YulangClosure.PaperTypes.PaperValueTyped.wrap' does not depend on any axioms

```

Bundled checker audit_source/validate_audit PASS for all8 theorems; constructor complete type/axiom output also retained. Standalone CLI avoided because it uses an unleased temporary directory.

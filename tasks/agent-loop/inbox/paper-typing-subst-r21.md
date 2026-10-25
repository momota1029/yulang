# R21 frozen tuple-split handoff — revision 1

Sprint `FULL-PAPER-TYPE-SUBSTITUTION-20261026/r21`, contract r1 SHA-256 `7bdab04134682ce01ebf723010c26a4d3a896cf2d024c8df0384f25cdc44d5ad`; baseline `b77fe13183e7ec80a95f08f919f34e832962c977`; worktree `/tmp/yulang-r21-split`. All7 frozen inputs and contract matched before any write/checker. Primary active receipt acknowledged in commit031103fe259e108bf389adfc08b5bdf2e669da7f before construction. Actual worker/sole author `/root/r17_forall`; requested registered lean_prover/role-default effort; observed model/effort UNKNOWN. Fresh runtime exposed shared CODEX_SESSION_ID01a172ef-fec1-72e3-bd47-bc4d7f51d6aa and CODEX_THREAD_ID01a1736a-fc42-7ab1-bc93-ddab8b55fa6d; no extra agent/session IDs inferred. No descendants.

Outcome: constructed and kernel-accepted candidate for represented split typing/inversion, tuple-introduction composition and arbitrary-σ support. Independent review and primary final checks PENDING; no self-certification, semantic-adoption, parent or production closure.

## Original claim, source and exact mapping

Original parent: `docs/yulang-operational-type-safety-ja.tex:953–977`, simultaneous type substitution for all paper typing judgments and original source scope. Source hash a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b. Relevant raw split syntax150–177; tuple introduction216 and split229; the latter types its body under Gamma,xbar:Abar with the original result. Whole-language/inference/executor parent remains `docs/yulang-whole-proof-closure-ja.md` §1. Current corrected-core V1(b) shared-substitution account is correspondence context, not replacement authority.

Ordering is grounded in the cited source's right-appended binder sequence and the actual existing let/value-lambda/continuation convention: one right-appended binder becomes one cons at environment head. Repeated cons for ordered types[A1,...,An] therefore gives reverse(types)++Gamma, with An at index0. No conflicting existing represented multi-binder convention was found. Arity is explicit equality of binder and component-type lengths; no zip, truncation, component reordering or extra context premise.

All exact delivered names have prefix `YulangClosure.PaperTypes.`:
- Definition `extendTupleEnvironment types environment := types.reverse ++ environment`, in Syntax. Its definition is printed in invocation2; it is not counted as a proved theorem.
- Theorem `mapTypeEnvironment_extendTupleEnvironment`: for arbitrary σ/types/Gamma, mapping the extended environment equals extending mapped component types over mapped Gamma. No formation, closedness or scope hypothesis.
- Constructor `PaperComputationTyped.split`: binders.length=types.length, tuple:argsSyntax types under D/Xi/Gamma, body:resultType under D/Xi/extendTupleEnvironment types Gamma; conclusion split(tuple,binders,body):resultType under the same D/Xi/Gamma. Constructor type and axiom report are printed separately.
- `PaperComputationTyped.splitInversion`: from typing the actual raw split at resultType, recovers the ordered type list, exact binder/type arity equality, scrutinee typing and body typing under the named extension, with exactly the original resultType index.
- `PaperComputationTyped.splitTuple`: from ValuesTyped values types, explicit binder/type arity and the original extended-body derivation, composes existing tuple introduction with split. Same ordered values/types; no runtime execution assertion.
- Extended `PaperValueTyped.subst_explicit`: new common recursor case retains the raw binder-name list, maps tuple/body by the same arbitrary σ, uses typingArgsSyntax_subst for ordered component types, List.length_map for arity and the extension commutation theorem for the body environment.
- Preserved/audited six transports: `PaperValueTyped.subst_explicit`, `ValuesTyped.typeTransport`, `ValuesAllTyped.typeTransport`, `RecordPayloadsTyped.typeTransport`, `PaperComputationTyped.typeTransport`, `PaperContinuationTyped.typeTransport`. All retain original arbitrary σ, D/Xi/Gamma and syntax/type indices; continuation response/result remain distinct.

Full fully qualified types and complete axiom reports appear below. This mapping does not replace those exact outputs.

## Scope, parent application and remaining owners

All38 previous constructors and premises retained; split adds one for39. Removing the helper/constructor additions recovers the old Syntax token sequence. Removing the extension theorem, new recursor case and2 split theorems recovers the prior TypingSubstitution token sequence. Raw split mapping and all prior wrap/union/forall/instantiation/record/operation/continuation cases remain untouched. No smaller source domain, new premise, witness change or restricted σ.

This applies directly to original paper229: exact tuple typing, arity and extended-body derivation construct the represented split conclusion; tuple introduction supplies the tuple premise from ordered ValuesTyped. The same rule is now covered by all6 arbitrary-substitution conclusions. This is typing composition only: it proves no split execution, term substitution or source/native runtime behavior.

Full parent stays OPEN. First missing original typing-rule premise in source order remains R18 variant typeArguments correspondence, owned by primary semantic/source intake; this packet neither interprets nor consumes it. Nominal, switch, remaining omitted rules, recursive graph guards, full paper substitution, inference/executor, original A/B and source/native/Rust/production bridges retain their existing owners. Primary owns the next exact rule-coverage/source-proof assignment and independent review. Proposition definitions and LocalLaws parameters remain distinct from concrete instances.

Formal path: paper tuple value derivation -> ordered ValuesTyped/argsSyntax -> split's exact extended-body premise -> simultaneous type-substitution transport -> inversion/typing composition. No constraint generator, actual execution consumer or native implementation correspondence was constructed. Implementation lane NO_SAFE_CODE_SLICE; no Rust/source-native right.

## Checks, complete axiom accounting and resources

Invocation1 native Lake `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake build +YulangClosure.PaperExecutionSyntax +YulangClosure.PaperExecutionTypingSubstitution`: exit0,21.260374s, including fresh dependency builds.
Invocation2 same Lake `env lean -j1 -M1024 .lake/R21Audit.lean`: exit0,0.651341s. Both cwd `/tmp/yulang-r21-split/notes/theory/lean`, LEAN_NUM_THREADS=1; project moreLeanArgs=-j1 -M1024.

Bundled `check_lean.py` audit_source/validate_audit PASS for all9 theorem declarations through the exact leased audit path. Standalone CLI was avoided because its temporary file would exceed the scratch lease. Axioms: the6 transports, splitInversion and splitTuple each exactly `[propext, Quot.sound]`; environment-extension commutation exactly `[propext]`; split constructor `does not depend on any axioms`. No sorryAx, project axiom, Classical.choice or checker bypass. Six-module dependency-cone source inspection has no sorry/admit/axiom/native_decide/skipKernelTC token matches. No checker failure occurred, so the mandatory first-failure stop condition was never triggered. All complete outputs are retained below.

Read lean-toolchain/lakefile/manifest: pin Lean4.35.0, YulangClosure, no external packages. Native path is the established installed distribution. No new version-only or reconnaissance process ran, and no earlier version receipt is relabeled R21 evidence.

Resources: 2 literal serial Lake processes,21.911715 checker seconds; worker3–6 unused, primary7–8 reserved. No earlier packet budget transferred. Active model-time telemetry uninstrumented; primary retains the original shared900-active-second/120-checker-second envelope including intake/review/integration, without invented timing or renewal. Peak OS memory unmeasured; Lean limits explicitly/project bounded. No tests, installation/dependency/global-default changes, compiler/Rust/config/contract/current/shared-status/root-import/Git mutation, other-worker path, reviewer appointment, external contact or children.

## Frozen artifacts and cessation

Only the2 leased source files, exact R21Audit and this one handoff were authored. Dedicated worktree `.lake/build` holds generated focused-build artifacts; no main-checkout source writes. Both processes and tool sessions returned exit0. No active command, checker session or descendant remains. After this final handoff write, all source/scratch/handoff/cache writes STOPPED. Dedicated cache ownership returns to primary for reserved final checks. Independent review/semantic qualification remain pending.

Frozen dependency/artifact SHA-256:
- `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean`: `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`
- `notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean`: `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `notes/theory/lean/YulangClosure/PaperTypeFormation.lean`: `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `notes/theory/lean/YulangClosure/DeclSubst.lean`: `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- `docs/yulang-operational-type-safety-ja.tex`: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`: `e025922217e5c5fc6d68780936acd99ac8252267f8c262b50da790a72cf73b0e`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`: `db213de9e97d965fb5e105f75009c9ec4f64e02892e5fdf3a8132317cc5e5f1d`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperExecutionSyntax.olean`: `5066e141d85df10032246a9e14e722653f12b84ced3077057def5d547e7a80f1`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperExecutionBinderLaws.olean`: `5ce648efad4bbcb77920c4ce44372d142777629ba68eaff65d270f0be9f61891`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperExecutionTypingSubstitution.olean`: `7b59f71a262bf0d2add638d5e354e9dfc66bcf58f8680ad6f36e859e332948d8`
- `notes/theory/lean/.lake/R21Audit.lean`: `6c612cd3a4025e2e8b709ce1ec32090bfc82de48c0e25fb86d88c64ee6cc93d7`

Full retained command/type/axiom evidence follows unchanged.

---

# R21 construction receipt (unfrozen)

Contract SHA-256 `7bdab04134682ce01ebf723010c26a4d3a896cf2d024c8df0384f25cdc44d5ad`; baseline `b77fe13183e7ec80a95f08f919f34e832962c977`. All7 frozen input hashes matched before writing. Primary receipt `031103fe259e108bf389adfc08b5bdf2e669da7f` acknowledged before any write/checker. Worker `/root/r17_forall`; actual runtime-exposed shared session `01a172ef-fec1-72e3-bd47-bc4d7f51d6aa`, thread `01a1736a-fc42-7ab1-bc93-ddab8b55fa6d`; requested registered lean_prover/role-default effort; observed model/effort UNKNOWN.

Source229 gives ordered Gamma,xbar:Abar. Existing let/value-lambda/continuation use cons for a single right-appended binder; repeated cons yields reverse types ++ Gamma. No conflicting represented multi-binder typing convention found. Split arity is explicit binder/type length equality; ValuesTyped preserves tuple component order.

Invocation1 `['/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', 'build', '+YulangClosure.PaperExecutionSyntax', '+YulangClosure.PaperExecutionTypingSubstitution']`; exit0; elapsed21.260374s; cwd `/tmp/yulang-r21-split/notes/theory/lean`
```text
✔ [1/5] Built YulangClosure.PaperTypeSubstitution (1.3s)
✔ [3/7] Built YulangClosure.PaperTypeFormation (8.5s)
✔ [4/7] Built YulangClosure.DeclSubst (262ms)
⚠ [5/7] Built YulangClosure.PaperExecutionSyntax (6.0s)
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
⚠ [6/7] Built YulangClosure.PaperExecutionBinderLaws (3.3s)
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
✔ [7/7] Built YulangClosure.PaperExecutionTypingSubstitution (724ms)
Build completed successfully (7 jobs).

```

Invocation2 `['/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', 'env', 'lean', '-j1', '-M1024', '.lake/R21Audit.lean']`; exit0; elapsed0.651341s; cwd `/tmp/yulang-r21-split/notes/theory/lean`
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
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.mapTypeEnvironment_extendTupleEnvironment
YulangClosure.PaperTypes.mapTypeEnvironment_extendTupleEnvironment : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  (types : List YulangClosure.PaperTypes.Ty) (environment : YulangClosure.PaperTypes.TypeEnvironment),
  YulangClosure.PaperTypes.mapTypeEnvironment σ (YulangClosure.PaperTypes.extendTupleEnvironment types environment) =
    YulangClosure.PaperTypes.extendTupleEnvironment (List.map (YulangClosure.PaperTypes.subst σ) types)
      (YulangClosure.PaperTypes.mapTypeEnvironment σ environment)
'YulangClosure.PaperTypes.mapTypeEnvironment_extendTupleEnvironment' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.PaperTypes.mapTypeEnvironment_extendTupleEnvironment
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperComputationTyped.splitInversion
@YulangClosure.PaperTypes.PaperComputationTyped.splitInversion : ∀
  {declarations : YulangClosure.PaperTypes.DeclarationTable} {graphTypes : YulangClosure.PaperTypes.GraphEnvironment}
  {environment : YulangClosure.PaperTypes.TypeEnvironment} {tuple : YulangClosure.PaperTypes.Value}
  {binders : List YulangClosure.PaperTypes.TermName} {body : YulangClosure.PaperTypes.Computation}
  {resultType : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes environment
      (YulangClosure.PaperTypes.Computation.split tuple binders body) resultType →
    ∃ types,
      binders.length = types.length ∧
        YulangClosure.PaperTypes.PaperValueTyped declarations graphTypes environment tuple
            (YulangClosure.PaperTypes.argsSyntax types) ∧
          YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes
            (YulangClosure.PaperTypes.extendTupleEnvironment types environment) body resultType
'YulangClosure.PaperTypes.PaperComputationTyped.splitInversion' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperComputationTyped.splitInversion
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperComputationTyped.splitTuple
@YulangClosure.PaperTypes.PaperComputationTyped.splitTuple : ∀
  {declarations : YulangClosure.PaperTypes.DeclarationTable} {graphTypes : YulangClosure.PaperTypes.GraphEnvironment}
  {environment : YulangClosure.PaperTypes.TypeEnvironment} {values : List YulangClosure.PaperTypes.Value}
  {types : List YulangClosure.PaperTypes.Ty} {binders : List YulangClosure.PaperTypes.TermName}
  {body : YulangClosure.PaperTypes.Computation} {resultType : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.ValuesTyped declarations graphTypes environment values types →
    binders.length = types.length →
      YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes
          (YulangClosure.PaperTypes.extendTupleEnvironment types environment) body resultType →
        YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes environment
          (YulangClosure.PaperTypes.Computation.split (YulangClosure.PaperTypes.Value.tuple values) binders body)
          resultType
'YulangClosure.PaperTypes.PaperComputationTyped.splitTuple' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperComputationTyped.splitTuple
@YulangClosure.PaperTypes.PaperComputationTyped.split : ∀ {declarations : YulangClosure.PaperTypes.DeclarationTable}
  {graphTypes : YulangClosure.PaperTypes.GraphEnvironment} {environment : YulangClosure.PaperTypes.TypeEnvironment}
  {tuple : YulangClosure.PaperTypes.Value} {binders : List YulangClosure.PaperTypes.TermName}
  {body : YulangClosure.PaperTypes.Computation} {types : List YulangClosure.PaperTypes.Ty}
  {resultType : YulangClosure.PaperTypes.Ty},
  binders.length = types.length →
    YulangClosure.PaperTypes.PaperValueTyped declarations graphTypes environment tuple
        (YulangClosure.PaperTypes.argsSyntax types) →
      YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes
          (YulangClosure.PaperTypes.extendTupleEnvironment types environment) body resultType →
        YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes environment
          (YulangClosure.PaperTypes.Computation.split tuple binders body) resultType
'YulangClosure.PaperTypes.PaperComputationTyped.split' does not depend on any axioms
def YulangClosure.PaperTypes.extendTupleEnvironment : List YulangClosure.PaperTypes.Ty →
  YulangClosure.PaperTypes.TypeEnvironment → YulangClosure.PaperTypes.TypeEnvironment :=
fun types environment => types.reverse ++ environment

```

Bundled audit_source/validate_audit PASS for all9 theorem declarations; constructor complete type/axioms and helper definition also retained. Exact leased audit output avoids the CLI temporary directory outside the lease.

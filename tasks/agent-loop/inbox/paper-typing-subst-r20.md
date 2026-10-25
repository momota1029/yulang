# R20 frozen union-elimination handoff — revision 1

Sprint `FULL-PAPER-TYPE-SUBSTITUTION-20261025/r20`, contract r1 SHA-256 `49166707d5fd483660672fd29f905fa38c3f0fc1f654b4569a6ea44beadb7743`. Baseline `aafbc15f0f9595eabea2c5187fba75fff06c3d04`; worktree `/tmp/yulang-r20-unioncase`. All6 frozen hashes matched before writing. Primary active receipt commit64fc1e5e7 cleared invocation1. Author/actual worker `/root/r17_forall`, requested registered lean_prover; observed model/effort UNKNOWN. Runtime-exposed shared session01a172ef-fec1-72e3-bd47-bc4d7f51d6aa and thread01a1736a-fc42-7ab1-bc93-ddab8b55fa6d were retained as observed identities, no new per-packet session inferred. Sole author; no descendants.

Outcome: constructed and kernel-accepted candidate for represented union elimination/inversion, both injection typing compositions and arbitrary-σ transport across all6 judgments. Independent review/primary final verification PENDING. No self-certification or parent/production closure.

## Original claim and exact source-to-Lean map

Original parent remains manuscript `docs/yulang-operational-type-safety-ja.tex:953–977`, simultaneous type substitution over the full paper judgments; whole-source goal remains `docs/yulang-whole-proof-closure-ja.md` §1. Governing union introduction/elimination line233 requires the two unioncase bodies to have the same result. Contract fixes the explicit left/right binder contexts, preserving the original quantifiers. Source hash a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b. Read the actual rule, syntax and substitution claim; current corrected-core V1(b) account supplies relevant shared-substitution context but no replacement semantic authority.

All delivered names have prefix `YulangClosure.PaperTypes.`:
- Constructor `PaperComputationTyped.unionCase`: v:A∨B under D/Xi/Γ, left:C under D/Xi/(A::Γ), right:C under D/Xi/(B::Γ), concludes unionCase(v,leftBinder,left,rightBinder,right):C under D/Xi/Γ.
- `PaperComputationTyped.unionCaseInversion`: from typing the actual raw unionCase at resultType, existentially recovers A/B and all3 premises. Both recovered branch judgments have exactly that original resultType index, so result equality is preserved directly, without an existential replacement result or extra equality premise.
- `PaperComputationTyped.unionCaseInjectLeft`: from v:A plus both original branch derivations, applies existing injectLeft then unionCase. Both branches remain required; binder types remain A/B respectively.
- `PaperComputationTyped.unionCaseInjectRight`: symmetric composition from v:B and both same branch premises, applying existing injectRight then unionCase.
- `PaperValueTyped.subst_explicit`: arbitrary-σ mutual recursor now includes unionCase; IH is applied to scrutinee and both branches with the same σ. Context cons mapping preserves left/right binder types and shared mapped tail. Raw binder names remain unchanged by the existing syntax mapping.
- Preserved and audited `ValuesTyped.typeTransport`, `ValuesAllTyped.typeTransport`, `RecordPayloadsTyped.typeTransport`, `PaperComputationTyped.typeTransport`, `PaperContinuationTyped.typeTransport`, with arbitrary σ, D/Xi/Γ, all syntax/type indices and separate continuation response/result.

Complete fully qualified theorem types and full axiom reports are retained in invocation2 below. The3 composition/inversion lemmas assert typing facts only; no branch evaluation, reduction, term substitution or runtime execution is claimed.

## Scope preservation and parent application

Prior37 constructors/premises retained; only unionCase added, giving38. Removing the new constructor block recovers original Syntax bytes exactly, including unchanged mapPaperComputation unionCase branch. Removing the new recursor case and3 theorem blocks recovers the prior TypingSubstitution token sequence. No existing wrapper, type-abstraction freshness, instantiation, record, operation, continuation or other premise changed. No narrower σ, type formation assumption, different shared environment or new witness.

The original represented unioncase premise is now constructible directly from its3 paper premises. Existing left/right introductions each compose with that rule while retaining both branches. The six substitution conclusions now cover this additional represented rule. The full paper parent remains OPEN: variant typeArguments correspondence (R18) and nominal/switch/remaining omitted typing rules, recursive graph guards, full inference/executor and original A/B/source-native/production bridges remain at their existing primary/source-proof owners. First unresolved original rule in paper order remains the separate variant correspondence premise; R20 does not consume or revise it. Primary owns subsequent exact proof/source packets, independent review and adjudication.

Formal path is raw unionCase + original branch derivations -> extrinsic constructor -> arbitrary-σ transport -> injection typing composition/inversion. No constraint generator, execution consumer, native implementation or concrete LocalLaws instance is constructed. No implementation lane or source/native right was granted.

## Actual verification and resources

Invocation1: installed native `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake build +YulangClosure.PaperExecutionSyntax +YulangClosure.PaperExecutionTypingSubstitution`, exit0,22.586330s, including fresh dependency builds.
Invocation2: same native Lake `env lean -j1 -M1024 .lake/R20Audit.lean`, exit0,0.686139s. Both cwd `/tmp/yulang-r20-unioncase/notes/theory/lean`, LEAN_NUM_THREADS=1, project moreLeanArgs=-j1 -M1024.

Bundled check_lean.py audit_source/validate_audit PASS for all9 named theorem declarations. The exact leased audit file is used to avoid the CLI's unleased temporary directory. Every theorem's complete axiom list is exactly `[propext, Quot.sound]`; unionCase constructor `does not depend on any axioms`. No sorryAx, project axiom, Classical.choice or checker bypass. Dependency-cone source inspection of all6 modules has no sorry/admit/axiom/native_decide/skipKernelTC token matches. No failed Lean declarations or repaired failure logs to omit; all output is retained below.

Pinned project: Lean4.35.0, YulangClosure library, no external packages, read lean-toolchain/lakefile/manifest. Native binary path is the established installed distribution. No new version/reconnaissance command was run; previous packet versions are not relabeled as new R20 observations.

2 literal serial Lake calls consumed,23.272469 checker seconds; worker3–4 unused, primary5–6 reserved. No previous call budget transferred. Active-time telemetry uninstrumented; no invented duration; work remained within the600-active-second/90-checker-second cap. No tests, install/dependency/global-default changes, Rust/compiler/contract/current/shared-status/configuration/Git mutation, root import, other-worker path, reviewer appointment, external contact or children.

## Cessation and frozen artifacts

Only the2 leased source modules, exact `.lake/R20Audit.lean` and this exact handoff were authored. Dedicated worktree `.lake/build` contains focused-build artifacts; no main-checkout source writes. Both invocation processes/sessions completed exit0. No active command or descendant remains. After this final handoff write, source/scratch/handoff/cache writes STOPPED. Cache ownership returns to primary for reserved final checks. Review and semantic/source qualification remain pending; this is not independent certification.

Frozen input/artifact SHA-256:
- `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean`: `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`
- `notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean`: `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `notes/theory/lean/YulangClosure/PaperTypeFormation.lean`: `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `notes/theory/lean/YulangClosure/DeclSubst.lean`: `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- `docs/yulang-operational-type-safety-ja.tex`: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`: `678f84eb635c95392068887b834a4f79a1a754ad474b950097aa212a3b68032c`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`: `55c84a4c3a5e83c3f4b8ff05b836790f0357b836d31daf0b9b316c427947afb7`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperExecutionSyntax.olean`: `6bf160c9b5ee1541eff029067edcaf771a29a793fb2d347f929b48d51bf430cb`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperExecutionBinderLaws.olean`: `ed7b891d96c75b2132d9aada19eee7296e9e740dde74287f045d4709afce7638`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperExecutionTypingSubstitution.olean`: `5a30de8388d65aafe0145da93ef9f67b70d977240370c07e29c1eab85b0e0136`
- `notes/theory/lean/.lake/R20Audit.lean`: `5e2fb4f6b9ba6f360201ac44637b8abf5aebd7d34987c864146ebaba19641f3d`

Full retained command/type/axiom output follows unchanged.

---

# R20 construction receipt (unfrozen)

Contract SHA-256 `49166707d5fd483660672fd29f905fa38c3f0fc1f654b4569a6ea44beadb7743`; baseline `aafbc15f0f9595eabea2c5187fba75fff06c3d04`. All6 frozen hashes matched. Primary active receipt `64fc1e5e7` cleared invocation1 before checker launch. Worker `/root/r17_forall`, shared runtime session `01a172ef-fec1-72e3-bd47-bc4d7f51d6aa`, thread `01a1736a-fc42-7ab1-bc93-ddab8b55fa6d`; observed model/effort UNKNOWN.

Invocation1 `['/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', 'build', '+YulangClosure.PaperExecutionSyntax', '+YulangClosure.PaperExecutionTypingSubstitution']`; exit0; elapsed22.586330s; cwd `/tmp/yulang-r20-unioncase/notes/theory/lean`
```text
✔ [1/5] Built YulangClosure.PaperTypeSubstitution (1.3s)
✔ [3/7] Built YulangClosure.PaperTypeFormation (9.2s)
✔ [4/7] Built YulangClosure.DeclSubst (305ms)
⚠ [5/7] Built YulangClosure.PaperExecutionSyntax (7.8s)
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
✔ [7/7] Built YulangClosure.PaperExecutionTypingSubstitution (614ms)
Build completed successfully (7 jobs).

```

Invocation2 `['/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', 'env', 'lean', '-j1', '-M1024', '.lake/R20Audit.lean']`; exit0; elapsed0.686139s; cwd `/tmp/yulang-r20-unioncase/notes/theory/lean`
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
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInversion
@YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInversion : ∀
  {declarations : YulangClosure.PaperTypes.DeclarationTable} {graphTypes : YulangClosure.PaperTypes.GraphEnvironment}
  {environment : YulangClosure.PaperTypes.TypeEnvironment} {value : YulangClosure.PaperTypes.Value}
  {leftBinder rightBinder : YulangClosure.PaperTypes.TermName} {left right : YulangClosure.PaperTypes.Computation}
  {resultType : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes environment
      (YulangClosure.PaperTypes.Computation.unionCase value leftBinder left rightBinder right) resultType →
    ∃ leftType rightType,
      YulangClosure.PaperTypes.PaperValueTyped declarations graphTypes environment value (leftType.union rightType) ∧
        YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes (leftType :: environment) left
            resultType ∧
          YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes (rightType :: environment) right
            resultType
'YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInversion' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInversion
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectLeft
@YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectLeft : ∀
  {declarations : YulangClosure.PaperTypes.DeclarationTable} {graphTypes : YulangClosure.PaperTypes.GraphEnvironment}
  {environment : YulangClosure.PaperTypes.TypeEnvironment} {value : YulangClosure.PaperTypes.Value}
  {leftBinder rightBinder : YulangClosure.PaperTypes.TermName} {left right : YulangClosure.PaperTypes.Computation}
  {leftType rightType resultType : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperValueTyped declarations graphTypes environment value leftType →
    YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes (leftType :: environment) left resultType →
      YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes (rightType :: environment) right
          resultType →
        YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes environment
          (YulangClosure.PaperTypes.Computation.unionCase value.injectLeft leftBinder left rightBinder right) resultType
'YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectLeft' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectLeft
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectRight
@YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectRight : ∀
  {declarations : YulangClosure.PaperTypes.DeclarationTable} {graphTypes : YulangClosure.PaperTypes.GraphEnvironment}
  {environment : YulangClosure.PaperTypes.TypeEnvironment} {value : YulangClosure.PaperTypes.Value}
  {leftBinder rightBinder : YulangClosure.PaperTypes.TermName} {left right : YulangClosure.PaperTypes.Computation}
  {leftType rightType resultType : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperValueTyped declarations graphTypes environment value rightType →
    YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes (leftType :: environment) left resultType →
      YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes (rightType :: environment) right
          resultType →
        YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes environment
          (YulangClosure.PaperTypes.Computation.unionCase value.injectRight leftBinder left rightBinder right)
          resultType
'YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectRight' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectRight
@YulangClosure.PaperTypes.PaperComputationTyped.unionCase : ∀ {declarations : YulangClosure.PaperTypes.DeclarationTable}
  {graphTypes : YulangClosure.PaperTypes.GraphEnvironment} {environment : YulangClosure.PaperTypes.TypeEnvironment}
  {value : YulangClosure.PaperTypes.Value} {leftBinder : YulangClosure.PaperTypes.TermName}
  {left : YulangClosure.PaperTypes.Computation} {rightBinder : YulangClosure.PaperTypes.TermName}
  {right : YulangClosure.PaperTypes.Computation} {leftType rightType resultType : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperValueTyped declarations graphTypes environment value (leftType.union rightType) →
    YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes (leftType :: environment) left resultType →
      YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes (rightType :: environment) right
          resultType →
        YulangClosure.PaperTypes.PaperComputationTyped declarations graphTypes environment
          (YulangClosure.PaperTypes.Computation.unionCase value leftBinder left rightBinder right) resultType
'YulangClosure.PaperTypes.PaperComputationTyped.unionCase' does not depend on any axioms

```

Bundled audit_source/validate_audit PASS for all9 theorem declarations. Constructor exact type/full axiom output also retained. No standalone CLI because its temporary output is outside the exact lease.

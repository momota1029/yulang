# Frozen R17.1 handoff — revision 1

Assignment `/root/r17_forall`; original parent `FULL-PAPER-TYPE-SUBSTITUTION-20261025/r17`. Original contract SHA-256 `510823d707f36c8cc33601d7d1ab78e2732015010ca705f74e1ed48c28fa69b3`; amendment `183b789f4bb87c45cbe72074061763e65f93a733e8dce006d3e2dea11d7c0450`. Isolated assigned baseline `aacb81609` (the original contract's earlier baseline label remains historical). Author is this registered leaf; no contributors or descendants. Requested role `lean_prover`; observed model/effort/session UUID UNKNOWN. Fresh resumption and runtime cessation receipts were sent to primary.

Outcome: constructed and kernel-accepted candidate proof of substitution transport for all six represented judgments, with the exact value-only universal introduction. Independent review and primary final verification PENDING. No semantic adoption, full-paper closure, native/Rust correspondence, inference/executor safety, original A/B closure or production authority is claimed.

Source: `docs/yulang-operational-type-safety-ja.tex`, typing/freshness lines203–207 and universal rule line237; original simultaneous type-substitution lemma lines953–977. Source SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`. Corrections: `notes/theory/2026-10-24-corrected-core-value-continuation.md` §2 V1(b), whose shared-context/same-substitution account informs correspondence but is not treated as independent semantic authority; whole parent `docs/yulang-whole-proof-closure-ja.md` §1 remains open.

Exact delivered theorem names, all prefixed `YulangClosure.PaperTypes.`:
- `PaperValueTyped.subst_explicit`
- `ValuesTyped.typeTransport`
- `ValuesAllTyped.typeTransport`
- `RecordPayloadsTyped.typeTransport`
- `PaperComputationTyped.typeTransport`
- `PaperContinuationTyped.typeTransport`
- `typeAbstractionSharedVariable`
- `typeAbstractionSharedContexts`

The six transports quantify over arbitrary `σ : Nat → Ty` and arbitrary D/Xi/Gamma, input syntax and type indices. Their sole typing premise is the original judgment. Conclusions map D, Xi, Gamma and syntax together; types use `subst σ`; lists retain all elements; continuation response and result remain distinct. Complete exact fully qualified printed types appear in invocation6 below.

`PaperValueTyped.typeAbstraction` is a constructor, not a theorem: its value body is typed under D/Xi/Gamma all shifted by `fun index => Ty.var (index+1)`, definitionally identical to downstream `shiftTypeSubstitution`; result is `.poly bodyType`. This avoids importing BinderLaws into Syntax and avoids changing its frozen definition. The recursor motive universally quantifies σ; the binder body uses `liftSub σ` and the accepted R16 declaration-table/graph/type-environment commutation laws. Raw syntax binder mapping already uses `liftSub σ`; accepted BinderLaws was rebuilt from the changed Syntax bytes in invocation3. No BinderLaws edits.

The explicit shared-context application includes an operation declaration with payload/response `var0`, graph entry `(5,var0)`, and Gamma `[var0]`; all shift to `var1`. The captured variable's result is `poly(var1)`, keeping that variable free beneath the fresh binder. No fresh witness, narrowing, closed-context condition, or freshness assumption was added.

Coverage: all prior35 constructors retained byte-for-byte apart from the six index headers; the only constructor addition is typeAbstraction, for36 total. This was checked by reversing those header edits and deleting the new constructor block, recovering the original Syntax bytes exactly. Includes records/presence/requiredness/uniqueness, shared intersection value, both lambda entries, operation resolution/arity/instance equality, request payload/continuation response/result correlation, type application and recursive roll/unroll instantiation.

Omissions/parent application: R17 removes the represented forall-introduction/transport obstruction. It proves neither complete paper typing nor typing for omitted raw constructors. The first missing introduction in the manuscript's typing-table order is variant payload/tag/arity typing (`Value.variant`); nominal introduction, wrap, remaining eliminations, handlers/maps/templates/primitives, recursive graph guard and full administrative cases also require faithful rules and transports. The primary owns the next full-paper rule-coverage/source-proof packet. Concrete executor/inference/source-native bridges retain their existing owners and OPEN status. No proposition definition or assumed LocalLaws is promoted to a concrete instance.

Verification: pinned Lean4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake5.0.0-src+eb6cafb. Five charged pre-amendment literal invocations are preserved, including two unauthorized version-query incidents; invocation6 is the direct audit. Invocations3/4 failed with full diagnostics retained below; invocation5 focused build PASS. Invocation6 exit0,2.336589s; bundled `audit_source` and `validate_audit` PASS for all eight theorem declarations. The helper CLI's unleased temporary directory was avoided by generating into exact leased `.lake/R17Audit.lean`. Every theorem's complete axiom list is exactly `[propext, Quot.sound]`; the new constructor reports the same. All six judgment signatures were also printed. No sorryAx, Classical.choice, project axiom or checker bypass. The six-source dependency cone has no sorry/admit/axiom/native_decide/skipKernelTC token matches.

Resources: six literal serial Lake invocations consumed, ~31.146 checker seconds total; invocation6 alone2.336589s. No version query was repeated after amendment. Worker invocations7–10 unused;11–12 remain reserved for primary. Original admission origin and1800-active-second/180-checker-second ceilings retained, no renewed budget. Exact accumulated model active-time telemetry unavailable; no fabricated timing receipt. Each actual Lean invocation inherited project `-j1 -M1024`; audit explicitly passed both and LEAN_NUM_THREADS=1. No tests, dependency installation, global-default edits, compiler/Rust/configuration/Git mutations or contact outside the team.

Writes and cessation: only the two leased source files, exact R17Audit scratch and this handoff were authored. Worktree-local `.lake/build` artifacts were generated by focused Lake builds; no main-checkout writes. All six invocations returned completion (exits0,0,1,1,0,0); no running subprocess session or spawned agent remains. No descendants. After this final handoff write, source/scratch/handoff/cache writes STOPPED. Primary may take the frozen artifacts/cache for final calls11–12 and independent review. No further leaf work is scheduled.

Frozen artifact/dependency SHA-256:
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`: `8f4a32fd1c013ae78a161dadd52bed57cc7c99af5ae30fd30ba133de2c3f74a4`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`: `b2975d38fccbf5c908741c3714b2b513b4b8706d80f3c009125c815d1b944d89`
- `notes/theory/lean/.lake/R17Audit.lean`: `05e22fc223be25f2d7fc8894f8204e79e6040a3e5d6a344a419594ecbdbc9260`
- `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean`: `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`
- `notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean`: `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `notes/theory/lean/YulangClosure/PaperTypeFormation.lean`: `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `notes/theory/lean/YulangClosure/DeclSubst.lean`: `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`

Full retained diagnostics and exact invocation receipts follow. Earlier status/round labels are historical evidence.

---

# R17.1 resumption and invocation correction

Contract amendment SHA-256 `183b789f4bb87c45cbe72074061763e65f93a733e8dce006d3e2dea11d7c0450`; original R17 `510823d707f36c8cc33601d7d1ab78e2732015010ca705f74e1ed48c28fa69b3`.
STOP was confirmed. No commands/processes/descendants/writes occurred after the pause until this authorized resumption confirmation. R17Audit did not exist. Stopped hashes:
- Syntax: `8f4a32fd1c013ae78a161dadd52bed57cc7c99af5ae30fd30ba133de2c3f74a4`.
- TypingSubstitution: `b2975d38fccbf5c908741c3714b2b513b4b8706d80f3c009125c815d1b944d89`.
- Prior handoff: `635969c5c863335dc8ccc8c7b39da81b947c30b7e5c1b98ea84d53ed77ae3686`.

All version/build subprocesses had cwd `/tmp/yulang-r17-forall/notes/theory/lean`; native Lake path `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`. The complete retained diagnostics follow below, unabridged. Correct literal invocation numbering:
1. `lake --version`: exit 0, 0.415s, Lake 5.0.0-src+eb6cafb / Lean 4.35.0. Protocol incident, charged.
2. `lake env lean --version`: exit 0, 0.083s, Lean4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc. Protocol incident, charged.
3. `lake build +YulangClosure.PaperExecutionSyntax +YulangClosure.PaperExecutionBinderLaws +YulangClosure.PaperExecutionTypingSubstitution`: exit 1,24.568s; missing final arbitrary σ application. Syntax and accepted BinderLaws rebuilt successfully.
4. `lake build +YulangClosure.PaperExecutionTypingSubstitution`: exit 1,3.006s; explicit continuation owners/binder inference and concrete record layout failed.
5. Same focused typing build: exit 0,0.737s; repaired via computation transport then continuation introduction, and explicit record layout.

The earlier `Call 2`/`Call 3` labels below mean construction rounds and correspond to literal invocations 4/5. No diagnostics are removed. Invocations6–10 remain worker-owned;11–12 primary-reserved. No version queries will repeat.

# R17 construction receipt (unfrozen)


Command: `['/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', '--version']`; exit 0; elapsed 0.415s
```text
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)

```

Command: `['/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', 'env', 'lean', '--version']`; exit 0; elapsed 0.083s
```text
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)

```

Command: `['/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', 'build', '+YulangClosure.PaperExecutionSyntax', '+YulangClosure.PaperExecutionBinderLaws', '+YulangClosure.PaperExecutionTypingSubstitution']`; exit 1; elapsed 24.568s
```text
✔ [1/6] Built YulangClosure.PaperTypeSubstitution (5.0s)
✔ [3/7] Built YulangClosure.PaperTypeFormation (8.4s)
✔ [4/7] Built YulangClosure.DeclSubst (266ms)
⚠ [5/7] Built YulangClosure.PaperExecutionSyntax (6.8s)
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
✖ [7/7] Building YulangClosure.PaperExecutionTypingSubstitution (664ms)
trace: .> LEAN_PATH=/tmp/yulang-r17-forall/notes/theory/lean/.lake/build/lib/lean /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 /tmp/yulang-r17-forall/notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean -o /tmp/yulang-r17-forall/notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperExecutionTypingSubstitution.olean -i /tmp/yulang-r17-forall/notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperExecutionTypingSubstitution.ilean -c /tmp/yulang-r17-forall/notes/theory/lean/.lake/build/ir/YulangClosure/PaperExecutionTypingSubstitution.c --setup /tmp/yulang-r17-forall/notes/theory/lean/.lake/build/ir/YulangClosure/PaperExecutionTypingSubstitution.setup.json --json
error: YulangClosure/PaperExecutionTypingSubstitution.lean:120:2: Type mismatch
  rec (fun {declarations} {graphTypes} {environment} σ => ValuesTyped.nil)
    (fun {declarations} {graphTypes} {environment} {value} {values} {ty} {types} hvalue hvalues ihValue ihValues σ =>
      have ihValue := ihValue σ;
      have ihValues := ihValues σ;
      Eq.mpr
        (id
          (congr
            (congrArg
              (ValuesTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (List.map (subst σ) environment))
              List.map_cons)
            List.map_cons))
        (ValuesTyped.cons ihValue ihValues))
    (fun {declarations} {graphTypes} {environment} {ty} σ => ValuesAllTyped.nil)
    (fun {declarations} {graphTypes} {environment} {value} {values} {ty} hvalue hvalues ihValue ihValues σ =>
      have ihValue := ihValue σ;
      have ihValues := ihValues σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (ValuesAllTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (List.map (subst σ) environment))
              List.map_cons)
            (subst σ ty)))
        (ValuesAllTyped.cons ihValue ihValues))
    (fun {declarations} {graphTypes} {environment} {recordType} σ => RecordPayloadsTyped.nil)
    (fun {declarations} {graphTypes} {label} {tag} {value} {fields} {recordType} {presence} {fieldType} {environment}
        hfield hvalue hfields ihValue ihFields σ =>
      have ihValue := ihValue σ;
      have ihFields := ihFields σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (RecordPayloadsTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              List.map_cons)
            (subst σ recordType)))
        (RecordPayloadsTyped.cons (RecordField.subst σ hfield) ihValue ihFields))
    (fun {declarations} {graphTypes} {environment} {index} {ty} lookup σ =>
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperValueTyped (mapDeclarationTable σ graphTypes) (mapGraphEnvironment σ environment)
                (mapTypeEnvironment σ declarations))
              (mapPaperValue.eq_1 σ index))
            (subst σ ty)))
        («variable»
          (Eq.mpr
            (id
              (Eq.trans (congrFun' (congrArg Eq (lookupTypeEnvironment_subst σ declarations index)) (some (subst σ ty)))
                Option.map_eq_some_iff._simp_1))
            (Eq.mp Option.map_eq_some_iff._simp_1 (congrArg (Option.map (subst σ)) lookup)))))
    (fun {declarations} {graphTypes} {environment} {identity} {ty} lookup σ =>
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperValueTyped (mapDeclarationTable σ graphTypes) (mapGraphEnvironment σ declarations)
                (mapTypeEnvironment σ environment))
              (mapPaperValue.eq_2 σ identity))
            (subst σ ty)))
        (graphReference
          (Eq.mpr
            (id
              (Eq.trans
                (congrFun' (congrArg Eq (lookupGraphEnvironment_subst σ declarations identity)) (some (subst σ ty)))
                Option.map_eq_some_iff._simp_1))
            (Eq.mp Option.map_eq_some_iff._simp_1 (congrArg (Option.map (subst σ)) lookup)))))
    (fun {declarations} {graphTypes} {environment} {literal} σ =>
      Eq.mpr
        (id
          (congr
            (congrArg
              (PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (mapPaperValue.eq_3 σ literal))
            (literalType_subst σ literal)))
        PaperValueTyped.literal)
    (fun {declarations} {graphTypes} {environment} {values} {types} hvalues ihValues σ =>
      have ihValues := ihValues σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (Eq.trans (mapPaperValue.eq_4 σ values)
                (congrArg Value.tuple
                  (Eq.trans
                    (List.map_subtype
                      (Eq.mpr (Eq.refl (∀ (x : Value), x ∈ values → mapPaperValue σ x = mapPaperValue σ x)) fun x h =>
                        rfl))
                    (congrArg (List.map (mapPaperValue σ)) List.unattach_attach)))))
            (subst σ (argsSyntax types))))
        (Eq.mp
          (congrArg
            (PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
              (mapTypeEnvironment σ environment) (Value.tuple (List.map (mapPaperValue σ) values)))
            (typingArgsSyntax_subst σ types))
          (tuple ihValues)))
    (fun {declarations} {graphTypes} {environment} {values} {elementType} hvalues ihValues σ =>
      have ihValues := ihValues σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperValueTyped
                { operations := List.map (OperationDeclaration.substAmbient σ) declarations.operations,
                  nominalConstructors := List.map (mapNominalConstructor σ) declarations.nominalConstructors,
                  primitives := List.map (mapPrimitiveSignature σ) declarations.primitives,
                  templates := List.map (mapTemplateBody σ) declarations.templates,
                  nativeListIdentity := declarations.nativeListIdentity }
                (mapGraphEnvironment σ graphTypes) (mapTypeEnvironment σ environment))
              (Eq.trans (mapPaperValue.eq_5 σ values)
                (congrArg Value.sequence
                  (Eq.trans
                    (List.map_subtype
                      (Eq.mpr (Eq.refl (∀ (x : Value), x ∈ values → mapPaperValue σ x = mapPaperValue σ x)) fun x h =>
                        rfl))
                    (congrArg (List.map (mapPaperValue σ)) List.unattach_attach)))))
            (Ty.nominal declarations.nativeListIdentity ((subst σ elementType).tupleCons Ty.tupleNil))))
        (sequence ihValues))
    (fun {declarations} {graphTypes} {environment} {fields} {recordType} {labels required} shape unique allRequired
        hfields ihFields σ =>
      have ihFields := ihFields σ;
      have unique' := Eq.mpr (id (congrArg List.Nodup (mapRecordFields_labels σ fields))) unique;
      have required' :=
        Eq.mpr
          (id
            (forall_congr fun label =>
              implies_congr (Eq.refl (label ∈ required))
                (congrFun' (congrArg Membership.mem (mapRecordFields_labels σ fields)) label)))
          allRequired;
      have result := record (RecordShape.subst σ shape) unique' required' ihFields;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (mapPaperValue_record_eq σ fields))
            (subst σ recordType)))
        result)
    (fun {declarations} {graphTypes} {environment} {body} {resultType} hbody ihBody σ =>
      have ihBody := ihBody σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (mapPaperValue.eq_10 σ body))
            (subst σ resultType).thunk))
        (delay ihBody))
    (fun {declarations} {graphTypes} {environment} {profile} {parameter} {body} {inputType outputType} hbody ihBody σ =>
      have ihBody := ihBody σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (List.map (subst σ) environment))
              (mapPaperValue.eq_9 σ EntryMode.value profile parameter body))
            ((subst σ inputType).callable (subst σ outputType))))
        (valueLambda ihBody))
    (fun {declarations} {graphTypes} {environment} {profile} {parameter} {body} {inputType outputType} hbody ihBody σ =>
      have ihBody := ihBody σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (List.map (subst σ) environment))
              (mapPaperValue.eq_9 σ EntryMode.computation profile parameter body))
            ((subst σ inputType).callable (subst σ outputType))))
        (computationLambda ihBody))
    (fun {declarations} {graphTypes} {environment} {value} {left right} hvalue ihValue σ =>
      have ihValue := ihValue σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (mapPaperValue.eq_14 σ value))
            ((subst σ left).union (subst σ right))))
        (injectLeft ihValue))
    (fun {declarations} {graphTypes} {environment} {value} {left right} hvalue ihValue σ =>
      have ihValue := ihValue σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (mapPaperValue.eq_15 σ value))
            ((subst σ left).union (subst σ right))))
        (injectRight ihValue))
    (fun {declarations} {graphTypes} {environment} {value} {left right} hleft hright ihLeft ihRight σ =>
      have ihLeft := ihLeft σ;
      have ihRight := ihRight σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (mapPaperValue.eq_16 σ value))
            ((subst σ left).intersection (subst σ right))))
        (both ihLeft ihRight))
    (fun {declarations} {graphTypes} {environment} {value} {ty} hvalue ihValue σ =>
      have ihValue := ihValue σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (mapPaperValue.eq_18 σ value))
            Ty.top))
        (topView ihValue))
    (fun {declarations} {graphTypes} {environment} {metadata} {value} {ty} hvalue ihValue σ =>
      have ihValue := ihValue σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (mapPaperValue.eq_19 σ metadata value))
            (subst σ ty)))
        (view ihValue))
    (fun {declarations} {graphTypes} {environment} {owners} {binder} {body} {responseType resultType} hcontinuation
        ihContinuation σ =>
      have ihContinuation := ihContinuation σ;
      have ihContinuation' :=
        Eq.mp
          (congrFun'
            (congrFun'
              (congrArg
                (PaperContinuationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                  (mapTypeEnvironment σ environment))
                (mapPaperValue.eq_20 σ owners binder body))
              (subst σ responseType))
            (subst σ resultType))
          ihContinuation;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (mapPaperValue.eq_20 σ owners binder body))
            ((subst σ responseType).kont (subst σ resultType))))
        (continuation ihContinuation'))
    (fun {declarations} {graphTypes} {environment} {body} {bodyType} hbody ihBody σ =>
      have transported := ihBody (liftSub σ);
      id
        (fun transported =>
          Eq.mpr
            (id
              (congrFun'
                (congrArg
                  (PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                    (mapTypeEnvironment σ environment))
                  (mapPaperValue.eq_12 σ body))
                (subst (liftSub σ) bodyType).poly))
            (typeAbstraction
              (Eq.mp
                (congrArg
                  (fun _a =>
                    PaperValueTyped (mapDeclarationTable shiftTypeSubstitution (mapDeclarationTable σ declarations))
                      (mapGraphEnvironment shiftTypeSubstitution (mapGraphEnvironment σ graphTypes)) _a
                      (mapPaperValue (liftSub σ) body) (subst (liftSub σ) bodyType))
                  (mapTypeEnvironment_shift_substitution_commutes σ environment))
                (Eq.mp
                  (congrArg
                    (fun _a =>
                      PaperValueTyped (mapDeclarationTable shiftTypeSubstitution (mapDeclarationTable σ declarations))
                        _a (mapTypeEnvironment (liftSub σ) (mapTypeEnvironment shiftTypeSubstitution environment))
                        (mapPaperValue (liftSub σ) body) (subst (liftSub σ) bodyType))
                    (mapGraphEnvironment_shift_substitution_commutes σ graphTypes))
                  (Eq.mp
                    (congrArg
                      (fun _a =>
                        PaperValueTyped _a
                          (mapGraphEnvironment (liftSub σ) (mapGraphEnvironment shiftTypeSubstitution graphTypes))
                          (mapTypeEnvironment (liftSub σ) (mapTypeEnvironment shiftTypeSubstitution environment))
                          (mapPaperValue (liftSub σ) body) (subst (liftSub σ) bodyType))
                      (have this := mapDeclarationTable_shift_substitution_commutes 0 σ declarations;
                      this))
                    transported)))))
        transported)
    (fun {declarations} {graphTypes} {environment} {function} {body argument} hfunction ihFunction σ =>
      have ihFunction := ihFunction σ;
      have ihFunction' := ihFunction;
      have commuteRaw := instantiateType_subst [argument] σ 1 rfl body;
      have commute :=
        id
          (Eq.mp
            (congrArg (Eq (subst σ (subst (instantiateSubstitution [argument]) body)))
              (congrFun'
                (congrArg subst
                  (congrArg instantiateSubstitution
                    (Eq.trans List.map_cons (congrArg (List.cons (subst σ argument)) List.map_nil))))
                (subst (liftSub σ) body)))
            commuteRaw);
      have result := typeApplication ihFunction';
      have result' :=
        Eq.mpr
          (id
            (congrFun'
              (congrArg
                (PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                  (mapTypeEnvironment σ environment))
                (mapPaperValue.eq_13 σ function argument))
              (instantiateType [subst σ argument] (subst (liftSub σ) body))))
          result;
      Eq.mpr
        (id
          (congrArg
            (fun _a =>
              PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment) (mapPaperValue σ (function.typeApplication argument)) _a)
            commute))
        result')
    (fun {declarations} {graphTypes} {environment} {value} {body} hvalue ihValue σ =>
      have ihValue := ihValue σ;
      have commuteRaw := instantiateType_subst [body.mu] σ 1 rfl body;
      have commute :=
        id
          (Eq.mp
            (congrArg (Eq (subst σ (subst (instantiateSubstitution [body.mu]) body)))
              (congrFun'
                (congrArg subst
                  (congrArg instantiateSubstitution
                    (Eq.trans List.map_cons (congrArg (List.cons (subst (liftSub σ) body).mu) List.map_nil))))
                (subst (liftSub σ) body)))
            commuteRaw);
      have ihValue' :=
        Eq.mpr
          (id
            (congrArg
              (fun _a =>
                PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                  (mapTypeEnvironment σ environment) (mapPaperValue σ value) _a)
              (Eq.symm commute)))
          ihValue;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (mapPaperValue.eq_17 σ value))
            (subst (liftSub σ) body).mu))
        (roll ihValue'))
    (fun {declarations} {graphTypes} {environment} {value} {ty} hvalue ihValue σ =>
      have ihValue := ihValue σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperComputationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (mapPaperComputation.eq_1 σ value))
            (subst σ ty)))
        (PaperComputationTyped.ret ihValue))
    (fun {declarations} {graphTypes} {environment} {first body} {firstType resultType} hfirst hbody ihFirst ihBody σ =>
      have ihFirst := ihFirst σ;
      have ihBody := ihBody σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperComputationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (List.map (subst σ) environment))
              (mapPaperComputation.eq_2 σ first body))
            (subst σ resultType)))
        (PaperComputationTyped.letE ihFirst ihBody))
    (fun {declarations} {graphTypes} {environment} {thunk} {resultType} hthunk ihThunk σ =>
      have ihThunk := ihThunk σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperComputationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (mapPaperComputation.eq_3 σ thunk))
            (subst σ resultType)))
        (PaperComputationTyped.force ihThunk))
    (fun {declarations} {graphTypes} {environment} {function thunk} {argumentType resultType} hfunction hthunk
        ihFunction ihThunk σ =>
      have ihFunction := ihFunction σ;
      have ihThunk := ihThunk σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperComputationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (mapPaperComputation.eq_4 σ function thunk))
            (subst σ resultType)))
        (PaperComputationTyped.call ihFunction ihThunk))
    (fun {declarations} {graphTypes} {environment} {value} {recordType} {label} {fieldType} hvalue hfield ihValue σ =>
      have ihValue := ihValue σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperComputationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (mapPaperComputation.eq_7 σ value label))
            (subst σ fieldType)))
        (PaperComputationTyped.field ihValue (RecordField.subst σ hfield)))
    (fun {declarations} {graphTypes} {environment} {value} {recordType} {label} {presence} {fieldType} hvalue hfield
        ihValue σ =>
      have ihValue := ihValue σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperComputationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (mapPaperComputation.eq_8 σ value label))
            ((Ty.base Base.unit).union (subst σ fieldType))))
        (PaperComputationTyped.lookup ihValue (RecordField.subst σ hfield)))
    (fun {declarations} {graphTypes} {environment} {operation} {arguments} {payload} {declaration} resolved arity
        payloadTyping ihPayload σ =>
      have ihPayload := ihPayload σ;
      have resolved' := OperationDeclarationResolved.typeTransport σ resolved;
      have commute := operation_declaration_instantiation_subst declaration arguments σ arity;
      have payloadType := congrArg OperationInstance.payloadType commute;
      have responseType := congrArg OperationInstance.responseType commute;
      have payloadTyping' :=
        Eq.mpr
          (id
            (congrArg
              (fun _a =>
                PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                  (mapTypeEnvironment σ environment) (mapPaperValue σ payload) _a)
              (Eq.symm payloadType)))
          ihPayload;
      have arity' :=
        of_eq_true
          (Eq.trans (congrFun' (congrArg Eq (Eq.trans (List.length_map (subst σ)) arity)) declaration.typeArity)
            (eq_self declaration.typeArity));
      Eq.mpr
        (id
          (congrArg
            (fun _a =>
              PaperComputationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment)
                (mapPaperComputation σ (Computation.perform operation arguments payload)) _a)
            responseType))
        (Eq.mpr
          (id
            (congrFun'
              (congrArg
                (PaperComputationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                  (mapTypeEnvironment σ environment))
                (mapPaperComputation.eq_15 σ operation arguments payload))
              ((OperationDeclaration.substAmbient σ declaration).instantiate
                  (List.map (subst σ) arguments)).responseType))
          (PaperComputationTyped.perform resolved' arity' payloadTyping')))
    (fun {declarations} {graphTypes} {environment} {opInstance} {payload continuation} {declaration} {arguments}
        {resultType} resolved arity instanceEq payloadTyping continuationTyping ihPayload ihContinuation σ =>
      have ihPayload := ihPayload σ;
      have ihContinuation := ihContinuation σ;
      have resolved' := OperationDeclarationResolved.typeTransport σ resolved;
      have commute := operation_declaration_instantiation_subst declaration arguments σ arity;
      have instance' :=
        Eq.mpr
          (id
            (congrArg
              (fun _a =>
                OperationInstance.subst σ _a =
                  (OperationDeclaration.substAmbient σ declaration).instantiate (mapOperationArguments σ arguments))
              instanceEq))
          commute;
      have payloadType := congrArg OperationInstance.payloadType commute;
      have responseType := congrArg OperationInstance.responseType commute;
      have payloadTyping' :=
        Eq.mpr
          (id
            (congrArg
              (fun _a =>
                PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                  (mapTypeEnvironment σ environment) (mapPaperValue σ payload) _a)
              (Eq.symm payloadType)))
          ihPayload;
      have continuationTyping' :=
        Eq.mpr
          (id
            (congrArg
              (fun _a =>
                PaperContinuationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                  (mapTypeEnvironment σ environment) (mapPaperValue σ continuation) _a (subst σ resultType))
              (Eq.symm responseType)))
          ihContinuation;
      have arity' :=
        of_eq_true
          (Eq.trans (congrFun' (congrArg Eq (Eq.trans (List.length_map (subst σ)) arity)) declaration.typeArity)
            (eq_self declaration.typeArity));
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperComputationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (mapPaperComputation.eq_21 σ opInstance payload continuation))
            (subst σ resultType)))
        (PaperComputationTyped.request resolved' arity' instance' payloadTyping' continuationTyping'))
    (fun {declarations} {graphTypes} {environment} {continuation response} {responseType resultType} hcontinuation
        hresponse ihContinuation ihResponse σ =>
      have ihContinuation := ihContinuation σ;
      have ihResponse := ihResponse σ;
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperComputationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (mapPaperComputation.eq_5 σ continuation response))
            (subst σ resultType)))
        (PaperComputationTyped.resume ihContinuation ihResponse))
    (fun {declarations} {graphTypes} {environment} {value} {body} hvalue ihValue σ =>
      have ihValue := ihValue σ;
      have commuteRaw := instantiateType_subst [body.mu] σ 1 rfl body;
      have commute :=
        id
          (Eq.mp
            (congrArg (Eq (subst σ (subst (instantiateSubstitution [body.mu]) body)))
              (congrFun'
                (congrArg subst
                  (congrArg instantiateSubstitution
                    (Eq.trans List.map_cons (congrArg (List.cons (subst (liftSub σ) body).mu) List.map_nil))))
                (subst (liftSub σ) body)))
            commuteRaw);
      have ihValue' := ihValue;
      have result := PaperComputationTyped.unroll ihValue';
      have result' :=
        Eq.mpr
          (id
            (congrFun'
              (congrArg
                (PaperComputationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                  (mapTypeEnvironment σ environment))
                (mapPaperComputation.eq_10 σ value))
              (instantiateType [(subst (liftSub σ) body).mu] (subst (liftSub σ) body))))
          result;
      Eq.mpr
        (id
          (congrArg
            (fun _a =>
              PaperComputationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment) (mapPaperComputation σ (Computation.unroll value)) _a)
            commute))
        result')
    (fun {declarations} {graphTypes} {environment} {reason} {ty} σ =>
      Eq.mpr
        (id
          (congrFun'
            (congrArg
              (PaperComputationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                (mapTypeEnvironment σ environment))
              (mapPaperComputation.eq_20 σ reason))
            (subst σ ty)))
        PaperComputationTyped.fail)
    (fun {declarations} {graphTypes} {environment} {owners} {binder} {body} {responseType resultType} hbody ihBody σ =>
      have ihBody := ihBody σ;
      Eq.mpr
        (id
          (congrFun'
            (congrFun'
              (congrArg
                (PaperContinuationTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
                  (List.map (subst σ) environment))
                (mapPaperValue.eq_20 σ owners binder body))
              (subst σ responseType))
            (subst σ resultType)))
        (PaperContinuationTyped.continuation ihBody))
    derivation
has type
  ∀ (σ : Nat → Ty),
    PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
      (mapTypeEnvironment σ environment) (mapPaperValue σ value) (subst σ ty)
but is expected to have type
  PaperValueTyped (mapDeclarationTable σ declarations) (mapGraphEnvironment σ graphTypes)
    (mapTypeEnvironment σ environment) (mapPaperValue σ value) (subst σ ty)
Some required targets logged failures:
- YulangClosure.PaperExecutionTypingSubstitution
error: build failed

```

Call 2: `['/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', 'build', '+YulangClosure.PaperExecutionTypingSubstitution']`; exit 1; elapsed 3.006s
```text
⚠ [5/7] Replayed YulangClosure.PaperExecutionSyntax
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
⚠ [6/7] Replayed YulangClosure.PaperExecutionBinderLaws
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
✖ [7/7] Building YulangClosure.PaperExecutionTypingSubstitution (2.6s)
trace: .> LEAN_PATH=/tmp/yulang-r17-forall/notes/theory/lean/.lake/build/lib/lean /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 /tmp/yulang-r17-forall/notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean -o /tmp/yulang-r17-forall/notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperExecutionTypingSubstitution.olean -i /tmp/yulang-r17-forall/notes/theory/lean/.lake/build/lib/lean/YulangClosure/PaperExecutionTypingSubstitution.ilean -c /tmp/yulang-r17-forall/notes/theory/lean/.lake/build/ir/YulangClosure/PaperExecutionTypingSubstitution.c --setup /tmp/yulang-r17-forall/notes/theory/lean/.lake/build/ir/YulangClosure/PaperExecutionTypingSubstitution.setup.json --json
error: YulangClosure/PaperExecutionTypingSubstitution.lean:442:26: don't know how to synthesize implicit argument `value`
  @PaperValueTyped.subst_explicit σ declarations graphTypes environment (Value.continuation ?m.105 ?m.106 body✝)
    (response.kont result) (PaperValueTyped.continuation (continuation body))
context:
σ : Nat → Ty
declarations : DeclarationTable
graphTypes : GraphEnvironment
environment : TypeEnvironment
response result : Ty
owners✝ : List OwnerName
binder✝ : TermName
body✝ : Computation
body : PaperComputationTyped declarations graphTypes (response :: environment) body✝ result
⊢ Value
error: YulangClosure/PaperExecutionTypingSubstitution.lean:442:60: don't know how to synthesize implicit argument `binder`
  @PaperValueTyped.continuation declarations graphTypes environment ?m.105 ?m.106 body✝ response result
    (continuation body)
context:
σ : Nat → Ty
declarations : DeclarationTable
graphTypes : GraphEnvironment
environment : TypeEnvironment
response result : Ty
owners✝ : List OwnerName
binder✝ : TermName
body✝ : Computation
body : PaperComputationTyped declarations graphTypes (response :: environment) body✝ result
⊢ TermName
error: YulangClosure/PaperExecutionTypingSubstitution.lean:442:60: don't know how to synthesize implicit argument `owners`
  @PaperValueTyped.continuation declarations graphTypes environment ?m.105 ?m.106 body✝ response result
    (continuation body)
context:
σ : Nat → Ty
declarations : DeclarationTable
graphTypes : GraphEnvironment
environment : TypeEnvironment
response result : Ty
owners✝ : List OwnerName
binder✝ : TermName
body✝ : Computation
body : PaperComputationTyped declarations graphTypes (response :: environment) body✝ result
⊢ List OwnerName
error: YulangClosure/PaperExecutionTypingSubstitution.lean:442:90: don't know how to synthesize implicit argument `binder`
  @continuation declarations graphTypes environment ?m.105 ?m.106 body✝ response result body
context:
σ : Nat → Ty
declarations : DeclarationTable
graphTypes : GraphEnvironment
environment : TypeEnvironment
response result : Ty
owners✝ : List OwnerName
binder✝ : TermName
body✝ : Computation
body : PaperComputationTyped declarations graphTypes (response :: environment) body✝ result
⊢ TermName
error: YulangClosure/PaperExecutionTypingSubstitution.lean:442:90: don't know how to synthesize implicit argument `owners`
  @continuation declarations graphTypes environment ?m.105 ?m.106 body✝ response result body
context:
σ : Nat → Ty
declarations : DeclarationTable
graphTypes : GraphEnvironment
environment : TypeEnvironment
response result : Ty
owners✝ : List OwnerName
binder✝ : TermName
body✝ : Computation
body : PaperComputationTyped declarations graphTypes (response :: environment) body✝ result
⊢ List OwnerName
error: YulangClosure/PaperExecutionTypingSubstitution.lean:442:11: failed to infer `have` declaration type
error: YulangClosure/PaperExecutionTypingSubstitution.lean:471:55: unexpected identifier; expected '}'
error: YulangClosure/PaperExecutionTypingSubstitution.lean:479:34: unexpected token; expected '(', '[', '{' or '⦃'
Some required targets logged failures:
- YulangClosure.PaperExecutionTypingSubstitution
error: build failed

```

Call 3: `['/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', 'build', '+YulangClosure.PaperExecutionTypingSubstitution']`; exit 0; elapsed 0.737s
```text
⚠ [5/7] Replayed YulangClosure.PaperExecutionSyntax
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
⚠ [6/7] Replayed YulangClosure.PaperExecutionBinderLaws
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
✔ [7/7] Built YulangClosure.PaperExecutionTypingSubstitution (603ms)
Build completed successfully (7 jobs).

```

Literal invocation6: `['/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', 'env', 'lean', '-j1', '-M1024', '.lake/R17Audit.lean']`; cwd `/tmp/yulang-r17-forall/notes/theory/lean`; exit 0; elapsed 2.336589s
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
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.typeAbstractionSharedVariable
YulangClosure.PaperTypes.typeAbstractionSharedVariable : ∀ (declarations : YulangClosure.PaperTypes.DeclarationTable)
  (graphTypes : YulangClosure.PaperTypes.GraphEnvironment),
  YulangClosure.PaperTypes.PaperValueTyped declarations graphTypes [YulangClosure.PaperTypes.Ty.var 0]
    (YulangClosure.PaperTypes.Value.variable 0).typeAbstraction (YulangClosure.PaperTypes.Ty.var 1).poly
'YulangClosure.PaperTypes.typeAbstractionSharedVariable' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.typeAbstractionSharedVariable
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.typeAbstractionSharedContexts
YulangClosure.PaperTypes.typeAbstractionSharedContexts : have declarations :=
  {
    operations :=
      [{ identity := 7, typeArity := 0, payloadTemplate := YulangClosure.PaperTypes.Ty.var 0,
          responseTemplate := YulangClosure.PaperTypes.Ty.var 0 }],
    nominalConstructors := [], primitives := [], templates := [], nativeListIdentity := 9 };
(YulangClosure.PaperTypes.mapDeclarationTable YulangClosure.PaperTypes.shiftTypeSubstitution declarations).operations =
    [{ identity := 7, typeArity := 0, payloadTemplate := YulangClosure.PaperTypes.Ty.var 1,
        responseTemplate := YulangClosure.PaperTypes.Ty.var 1 }] ∧
  YulangClosure.PaperTypes.mapGraphEnvironment YulangClosure.PaperTypes.shiftTypeSubstitution
        [(5, YulangClosure.PaperTypes.Ty.var 0)] =
      [(5, YulangClosure.PaperTypes.Ty.var 1)] ∧
    YulangClosure.PaperTypes.mapTypeEnvironment YulangClosure.PaperTypes.shiftTypeSubstitution
          [YulangClosure.PaperTypes.Ty.var 0] =
        [YulangClosure.PaperTypes.Ty.var 1] ∧
      YulangClosure.PaperTypes.PaperValueTyped declarations [(5, YulangClosure.PaperTypes.Ty.var 0)]
        [YulangClosure.PaperTypes.Ty.var 0] (YulangClosure.PaperTypes.Value.variable 0).typeAbstraction
        (YulangClosure.PaperTypes.Ty.var 1).poly
'YulangClosure.PaperTypes.typeAbstractionSharedContexts' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.typeAbstractionSharedContexts
@YulangClosure.PaperTypes.PaperValueTyped.typeAbstraction : ∀ {declarations : YulangClosure.PaperTypes.DeclarationTable}
  {graphTypes : YulangClosure.PaperTypes.GraphEnvironment} {environment : YulangClosure.PaperTypes.TypeEnvironment}
  {body : YulangClosure.PaperTypes.Value} {bodyType : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperValueTyped
      (YulangClosure.PaperTypes.mapDeclarationTable (fun index => YulangClosure.PaperTypes.Ty.var (index + 1))
        declarations)
      (YulangClosure.PaperTypes.mapGraphEnvironment (fun index => YulangClosure.PaperTypes.Ty.var (index + 1))
        graphTypes)
      (YulangClosure.PaperTypes.mapTypeEnvironment (fun index => YulangClosure.PaperTypes.Ty.var (index + 1))
        environment)
      body bodyType →
    YulangClosure.PaperTypes.PaperValueTyped declarations graphTypes environment body.typeAbstraction bodyType.poly
'YulangClosure.PaperTypes.PaperValueTyped.typeAbstraction' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.ValuesTyped : YulangClosure.PaperTypes.DeclarationTable →
  YulangClosure.PaperTypes.GraphEnvironment →
    YulangClosure.PaperTypes.TypeEnvironment →
      List YulangClosure.PaperTypes.Value → List YulangClosure.PaperTypes.Ty → Prop
YulangClosure.PaperTypes.ValuesAllTyped : YulangClosure.PaperTypes.DeclarationTable →
  YulangClosure.PaperTypes.GraphEnvironment →
    YulangClosure.PaperTypes.TypeEnvironment → List YulangClosure.PaperTypes.Value → YulangClosure.PaperTypes.Ty → Prop
YulangClosure.PaperTypes.RecordPayloadsTyped : YulangClosure.PaperTypes.DeclarationTable →
  YulangClosure.PaperTypes.GraphEnvironment →
    YulangClosure.PaperTypes.TypeEnvironment →
      List (YulangClosure.PaperTypes.Label × YulangClosure.PaperTypes.Presence × YulangClosure.PaperTypes.Value) →
        YulangClosure.PaperTypes.Ty → Prop
YulangClosure.PaperTypes.PaperValueTyped : YulangClosure.PaperTypes.DeclarationTable →
  YulangClosure.PaperTypes.GraphEnvironment →
    YulangClosure.PaperTypes.TypeEnvironment → YulangClosure.PaperTypes.Value → YulangClosure.PaperTypes.Ty → Prop
YulangClosure.PaperTypes.PaperComputationTyped : YulangClosure.PaperTypes.DeclarationTable →
  YulangClosure.PaperTypes.GraphEnvironment →
    YulangClosure.PaperTypes.TypeEnvironment → YulangClosure.PaperTypes.Computation → YulangClosure.PaperTypes.Ty → Prop
YulangClosure.PaperTypes.PaperContinuationTyped : YulangClosure.PaperTypes.DeclarationTable →
  YulangClosure.PaperTypes.GraphEnvironment →
    YulangClosure.PaperTypes.TypeEnvironment →
      YulangClosure.PaperTypes.Value → YulangClosure.PaperTypes.Ty → YulangClosure.PaperTypes.Ty → Prop

```

Bundled checker `audit_source` and `validate_audit`: PASS for all eight theorem declarations; no standalone helper CLI because its temporary path is outside the exact lease. Constructor and six judgment signatures also printed above.

# R24 operation-mapper evidence — constructed, unchecked, frozen revision 1

Sprint `FULL-PAPER-TYPE-SUBSTITUTION-20261026/r24`; contract r1 SHA-256 `3f407f0d38eaf8b3e496708e7e40278a7e7cb7f9b1e048f230de2a53b57df297`; baseline `c2bd4055094e7b75a2155638611f015f0baa52ea`. Exact worktree `/tmp/yulang-r24-mapop`. Admission/leases acknowledged at5c5d4b6ec; actual launch receipt logged atcb2336487. Initial command in the assigned worktree failed to create a process because the directory was not yet provisioned; a read-only primary-checkout metadata lookup confirmed absence. Primary then provisioned this exact isolated baseline; all9 contract inputs matched there before writing and after construction. No primary-checkout write occurred.

Actual worker/sole author `/root/r17_forall`; fresh runtime exposed shared CODEX_SESSION_ID01a172ef-fec1-72e3-bd47-bc4d7f51d6aa and CODEX_THREAD_ID01a1736a-fc42-7ab1-bc93-ddab8b55fa6d. Requested registered lean_prover/role-default effort; observed model/effort UNKNOWN. No children or descendants.

Outcome class: constructed proof candidate, NOT kernel-checked. Source gate was reported PASS within the bounded adapter-premise scope, with precise evidence below; independent source/spec review remains pending. Primary owns checker/cache outputs under this packet, so this leaf has run zero Lean/Lake processes and makes no actual theorem-type/axiom result or proof acceptance claim. No full mapOperation rule or execution implementation is claimed.

## Original parent and source gate evidence

Parent remains full-paper simultaneous type substitution at `docs/yulang-operational-type-safety-ja.tex:953–977`, followed by inference/executor/A-B on the unchanged accepted source domain. Governing manuscript hash a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b.

Manuscript694–697 specifies one same family/member o, source instance Abar and target instance Bbar, payload code P_o(Abar)->P_o(Bbar), response code Q_o(Bbar)->Q_o(Abar), and the same mapper w in both directions. Lines700–709 apply a to p and r to z, fixing the actual input types. Lines711–717 retain free-code names under capture avoidance and execute adapter computations as ordinary code, without rebinding their captured environments. Line718 requires both actual syntactic code typings and matching operation signatures. Ordinary shared D/Gamma conventions are at202–207; omitted Xi is shared across all premises at269. The computation-code single-formal representation follows paper224 and accepted R19's exact cons convention; R19 is supporting de Bruijn representation evidence, while mapper-specific direction/inputs come from694–719 themselves.

Therefore the bounded premises use payload code under source.payloadType::Gamma returning target.payloadType, and response code under target.responseType::Gamma returning source.responseType; both share the same D/Xi/Gamma. This introduces no fresh type binder or registered-body opening: source/target are actual type instances of a single operation declaration, each with its own concrete witness list. Consequently R23's missing entry-local D/Xi embedding is not consumed or assumed. No Rust implementation convention supplied this mapping. This producer source audit is not independent certification or semantic adoption.

Accepted definitions were read directly: OperationDeclaration.instantiate stores argsSyntax of the witness list in OperationInstance.typeArguments (a Ty), plus payload/response substitution by instantiateSubstitution. mapMapperPlan maps both full instances and both computation bodies under the same σ. operation_declaration_instantiation_subst preserves that full equality, including encoded type arguments. Resolution uniqueness and actual body derivations remain explicit premises, not proved universally for generated source.

## Constructed declarations and exact premises

New module `YulangClosure.PaperOperationMapperTyping` imports only accepted PaperExecutionTypingSubstitution. All names below have prefix `YulangClosure.PaperTypes.`:

- `MapperPlanTyped declarations graphTypes environment mapper`: transparent inductive evidence with one constructor mk. For raw `.mk source target payload response`, it carries unique OperationDeclarationResolved at source.identity; sourceArguments.length=declaration.typeArity; targetArguments.length=that same arity; full source=declaration.instantiate sourceArguments; full target=declaration.instantiate targetArguments; actual payload computation typing under source.payloadType::environment at target.payloadType; actual response computation typing under target.responseType::environment at source.responseType. Every premise has the same declaration/graph/captured context. No encoded argument field is dropped.
- `MapperPlanTyped.inversion`: from actual mk-plan evidence, recovers the single declaration, both witness lists, both arity equations, both full instance equalities and both exact adapter derivations. No separate declaration/instance witness is selected for response code.
- `MapperPlanTyped.sameIdentity`: derives source.identity=target.identity from the full instance equalities; same operation identity is not inferred from matching payload/response types alone.
- `MapperPlanTyped.typeTransport σ`: arbitrary σ, D/Xi/Gamma/mapper. Conclusion is MapperPlanTyped(mapDeclarationTable σ D)(mapGraphEnvironment σ Xi)(mapTypeEnvironment σ Gamma)(mapMapperPlan σ mapper). Proof maps the same declaration by substAmbient, both lists by mapOperationArguments, preserves their exact arities/full instance equations via operation_declaration_instantiation_subst, and applies actual PaperComputationTyped.typeTransport to both computations with their same mapped captured tail. No σ formation/closedness restriction, new scope assumption, table invariance or witness change.

Constructed polarity data and theorems:
- mapperPolarityDeclaration: identity17, arity1, payload/response templates both var0.
- mapperPolaritySource: that exact declaration instantiated with `[Bool]`; mapperPolarityTarget: the same declaration instantiated with `[Int]`. Both complete instances include the encoded argument vector by the accepted instantiate definition.
- mapperPolarityGood and mapperPolarityBad have exactly the same source instance, target instance and Int-returning payload computation. Good response returns Bool; only Bad response changes to an Int literal return.
- `mapperPolarityGoodTyped`: constructs relation evidence using the literal witness lists `[Bool]`/`[Int]`, both exact arities and full equalities, payload under Bool returning Int, response under Int returning Bool.
- `mapperPolarityBadNotTyped`: negates the relation for the unchanged bad raw plan; inversion would supply an Int-returning literal derivation at Bool, eliminated by computation/value constructor inversion. This excludes every alternative relation witness, rather than switching witness lists to obtain the negative result. No paper counterexample or operational behavior is asserted.

These are constructed statements/terms only. There are no actual printed Lean types, kernel diagnostics or axiom outputs yet. The new relation is separate from the accepted six-judgment family and does not add `PaperComputationTyped.mapOperation`. Frozen R22 source files were not edited.

## Audit and exact primary handoff

Exact leased `.lake/R24Audit.lean` was generated using bundled check_lean.py audit_source. It contains checks for all5 new theorems, the2 declaration/instance dependency theorems and all6 existing common transports (13 complete theorem audits), plus relation/constructor signatures/axioms and raw positive/negative plan definitions. Generation is not validation; the source has NOT run and validate_audit has no actual output to consume.

Primary-only commands, NOT RUN by this leaf:
```text
cwd /tmp/yulang-r24-mapop/notes/theory/lean
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake build +YulangClosure.PaperOperationMapperTyping
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean -j1 -M1024 .lake/R24Audit.lean
```
After actual success, primary can validate complete output with bundled validate_audit and the exact13 theorem names already encoded in R24Audit. No theorem is labeled proved before that and independent review. Pinned project files were read: Lean4.35.0, YulangClosure, no external packages; no new version observation is invented.

## Parent application and remaining owners

If checked and independently reviewed, the relation supplies the two explicit adapter-code premises of paper718, and the new theorem transports those premises under one arbitrary type substitution of the actual mapper. It does not close the omitted mapOperation typing constructor, body/frame/continuation composition, term substitution, freshening or one-step preservation. Those remain primary/source-proof intake responsibilities. Neither side adapter is assumed safe merely because it has a matching signature: both actual typing derivations are required.

R23-TEMPLATE-CALLER-CONTEXT-EMBEDDING-1, R18 variant correspondence and the full paper/inference/executor/A-B/source-native/Rust/production goals remain OPEN. No conditional table-invariance theorem, stronger premise or smaller source language is substituted for those gates. NO_SAFE_CODE_SLICE remains; no Rust/constraint generator/execution consumer correspondence is claimed.

## Resources, source inspection and cessation

Worker Lean/Lake invocations0, checker seconds0, cache/generated-checker-output writes0. Primary retains checker ownership, original8-call/120-checker-second/1200-active-second envelope and two reserved calls; worker cap6 is unspent unless explicitly reassigned. Source-model active time uninstrumented; no invented duration or renewed budget. No test, dependency install/change, global-default edit, default/full build, network, compiler/Rust, root import, config/status/current/contract/index/reviewer/Git mutation, external contact or children.

All9 frozen input hashes rechecked unchanged. New module source inspection has no sorry/admit/project axiom/native_decide/skipKernelTC tokens; this static inspection is not an indirect axiom audit. Only the new leased module, exact R24Audit and this one handoff were written. The audit parent directory was created if absent; no `.lake/build` or other generated cache output was created by this leaf.

STOPPED: all commands returned, no active checker/process/subprocess session or descendant remains. After this final handoff write, module/audit/handoff writes STOPPED. Source edits require an explicit new writer handoff after primary checking; this artifact is frozen for actual verification and fresh non-author review.

Frozen input hashes:
- `docs/yulang-operational-type-safety-ja.tex`: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`: `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`: `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`
- `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean`: `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`
- `notes/theory/lean/YulangClosure/PaperTypeFormation.lean`: `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean`: `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `notes/theory/lean/YulangClosure/DeclSubst.lean`: `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- `tasks/agent-loop/inbox/paper-typing-subst-r23-adjudication.md`: `be099fabf7a7eea06b137ebc5862a1d0058da132356c06f369ec9fe8e635bcd1`
- `tasks/agent-loop/inbox/paper-typing-subst-r19-adjudication.md`: `b98075739888a5cb9a90e49166f78a39e79e44ed2659554c0f8ffecfa3664ed4`

Frozen authored artifacts:
- `notes/theory/lean/YulangClosure/PaperOperationMapperTyping.lean`: `175c307e00bea7ba6ec44ff153f50a7d9d943de8bdc3d4dccb02a41bc53dde77`
- `notes/theory/lean/.lake/R24Audit.lean`: `e72f5648afd52e144802c6e1f1f62808ff0693c23a23f80b0580bb88007786d3`

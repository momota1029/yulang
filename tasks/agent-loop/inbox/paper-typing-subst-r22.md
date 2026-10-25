# R22 constructed-but-unchecked handoff — frozen revision 1

Sprint `FULL-PAPER-TYPE-SUBSTITUTION-20261026/r22`, contract r1 SHA-256 `190841c2881a73ad66e9461642486bd01111cf9c037ea4bac28c7e60ef62b54b`; accepted R21 baseline `8ff731456dd9385f6497e9c5c0b99e7d8820a898`. Exact worktree `/tmp/yulang-r22-templatecall` was assigned after receipt acknowledgement commit2f5df4714. All7 frozen inputs matched both primary checkout for initial receipt and isolated worktree before writing. Primary checkout remained read-only. The initial guessed path `/tmp/yulang-r22-template-call` did not exist; that read-only path check made no writes and is not represented as the assigned worktree.

Actual worker/sole author `/root/r17_forall`; fresh runtime exposed shared CODEX_SESSION_ID01a172ef-fec1-72e3-bd47-bc4d7f51d6aa and CODEX_THREAD_ID01a1736a-fc42-7ab1-bc93-ddab8b55fa6d. Requested registered lean_prover/role-default effort; observed model/effort UNKNOWN. No children or contributing descendants.

Outcome class: constructed proof candidate, NOT Lean-checked. Primary explicitly owns every Lean/Lake invocation and `.lake/build`/cache; this leaf ran zero checkers and wrote zero generated cache artifacts. No type/axiom output, kernel acceptance, independent review or closure is claimed. Source/audit are frozen for primary's actual execution. This execution-ownership boundary, rather than a missing tool installation, prevents a leaf checker receipt.

## Original claim and source

Original mathematical parent is manuscript `docs/yulang-operational-type-safety-ja.tex:953–977`, simultaneous substitution for the full paper judgments, and original inference/executor/A-B goals over unchanged source scope. Source SHA-256 a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b. Read actual declaration-table condition129, invocation rule243 and substitution lemma953–977, plus actual TemplateBody/mapTemplateBody/DeclarationTable and common recursor. Rule243 has one declared code instance shared by formal types and result; actual values are typed against that formal list. Rule129 separately requires registered body typing under its prescribed formal environment. Current corrected-core/shared-substitution drafts supply context only, not new authority. Whole parent `docs/yulang-whole-proof-closure-ja.md` §1 remains OPEN.

The following fully qualified names have prefix `YulangClosure.PaperTypes.`; all theorem claims below describe constructed statements, not checked receipts:

1. Definition `templateIdentity : TemplateBody → Nat` reads only the lookup key; it does not replace the stored entry or discard any component.
2. Definition `TemplateDeclarationResolved templates identity declaration`: declaration membership, matching key, and uniqueness of the entire TemplateBody among entries with that key. Distinct bodies at the same key cannot meet this premise; identical repeated entries do not select distinct code. The full declaration remains the witness.
3. Theorem `templateIdentity_mapTemplateBody`: arbitrary σ preserves the key of the entire mapped entry.
4. Theorem `TemplateDeclarationResolved.typeTransport`: for arbitrary σ/templates/identity/declaration, resolution transports to `templates.map (mapTemplateBody σ)` and the same whole declaration mapped by mapTemplateBody. Uniqueness is pulled back through List.mem_map and original key uniqueness; substitution injectivity is not assumed. Actual body mapping is retained.
5. Constructor `PaperComputationTyped.template`: for arbitrary D/Xi/Gamma, identity, typeArguments, actual arguments, typeArity, formals, result and body, requires resolution of `.mk identity typeArity formals result body`, exact typeArguments.length=typeArity, and ValuesTyped for every actual against `formals.map (instantiateType typeArguments)`; concludes raw `.template identity typeArguments arguments` at `instantiateType typeArguments result`. Both instances literally use the same typeArguments vector; no extra witness, new scope condition or body-safety premise.
6. Theorem `instantiateFormalTypes_subst`: with the actual argument-length equality, maps every instantiated formal by arbitrary σ to instantiation of all mapped formals under `liftSubN typeArity σ` by the same mapped argument vector. It applies existing instantiateType_subst to each formal, with no new algebraic assumption.
7. Existing `PaperValueTyped.subst_explicit` common recursor: new template case transports resolution and exact type arity, transports ValuesTyped under arbitrary σ, rewrites the entire formal list by instantiateFormalTypes_subst, rewrites result by instantiateType_subst, and reuses constructor. The existing raw mapping retains identity and maps all raw type arguments/actual values under that same σ. mapTemplateBody retains and maps the executable body under the declaration's type binders.
8. Theorem `PaperComputationTyped.templateInversion`: from actual raw template typing at resultType, recovers typeArity/formals/result/body, unique resolution of that exact complete entry, exact invocation type-arity equality, all actual-argument typing at the single formal instance, and resultType=instantiateType typeArguments result.
9. Preserved six transport statements: `PaperValueTyped.subst_explicit`, `ValuesTyped.typeTransport`, `ValuesAllTyped.typeTransport`, `RecordPayloadsTyped.typeTransport`, `PaperComputationTyped.typeTransport`, `PaperContinuationTyped.typeTransport`. No statement/quantifier changes; response/result remain distinct; common proof has one additional case.

## Exact OPEN boundary and parent application

If primary's pinned focused build and complete audit accept these terms and independent source review accepts the correspondence, the represented invocation-instance premise of paper243 and its arbitrary-σ preservation are supplied. This is conditional on actual checking/review, not a present proof receipt. No definition of assumed body typing is introduced as a theorem.

Table-body condition129 remains OPEN: for the resolved stored entry, an actual body typing derivation must be constructed in the prescribed formal environment before invocation typing supports execution. Primary/source-proof intake owns that next premise. The actual TemplateBody witness is retained through resolution/inversion/mapping, so no different body can be substituted as a new witness. Full type/body/term instantiation and template execution require later exact proofs.

Original full-paper parent remains OPEN, including R18 variant correspondence, nominal/switch/other omitted forms, recursive graph guards, full inference/executor, A/B, source/native/Rust and production. No R18 interpretation was used. No constraint generator or Rust/runtime/native source mapping was constructed; NO_SAFE_CODE_SLICE remains. Proposition definitions and LocalLaws parameters are not concrete instances.

## Scope inspection and exact audit handoff

Prior39 constructors/premises preserved; one template constructor adds the40th. Removing only the new identity/resolver/constructor definitions and reverting the updated partial-coverage comment recovers the prior Syntax token sequence. Removing only the new helper/resolver/inversion theorems and common-recursion case recovers the prior TypingSubstitution token sequence. Existing mapTemplateBody, mapDeclarationTable, raw template mapping, all binder/record/operation/wrap/union/split cases and six transport statements are unchanged.

Source inspection of all6 modules in the dependency cone found no sorry/admit/axiom/native_decide/skipKernelTC token matches. This inspection is not an indirect axiom audit or kernel acceptance.

Exact leased `notes/theory/lean/.lake/R22Audit.lean` was generated with bundled check_lean.py audit_source for all10 named theorem declarations: six transports, formal-list commutation, identity preservation, resolver transport and inversion. It also checks/prints constructor axioms and prints templateIdentity, resolver and mapTemplateBody definitions to expose retained body mapping. The file has NOT been run; audit_source generation is not validation. There are no actual printed theorem types/axiom lists or diagnostic results yet.

Primary-only suggested invocation sequence, both NOT RUN by this leaf:
```text
cwd /tmp/yulang-r22-templatecall/notes/theory/lean
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake build +YulangClosure.PaperExecutionSyntax +YulangClosure.PaperExecutionTypingSubstitution
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean -j1 -M1024 .lake/R22Audit.lean
```
After the actual audit succeeds, run the bundled validate_audit on complete output with the exact10 names encoded in R22Audit. This requires real output; none is fabricated here. Primary owns every checker/cache write. No default/full build, version-only invocation, tests, install/dependencies or network call is proposed. Project pin Lean4.35.0 is unchanged; no new version observation is claimed.

Resources: worker Lean/Lake invocations0, checker seconds0, cache writes0. Worker cap6 remains unspent unless separately reassigned; primary controls original total8-call/120-checker-second/900-active-second envelope. Active model time uninstrumented, no renewal or invented measurement. No compiler/Rust/config/status/contract/current/root-import/Git mutation, other worker path, appointments, external contact or descendants.

## Frozen outputs and cessation

Only the2 leased source modules, exact R22Audit and this handoff were written. No `.lake/build`, generated outputs or primary-checkout files were changed by this leaf. All read/edit commands completed; no outstanding checker process, subprocess session or descendant exists. After this final handoff write all source/audit/handoff writes STOPPED. Cache ownership remained primary throughout. Primary may now run the pinned build/audit and assign fresh non-author review; source fixes require a new explicit writer handoff.

Frozen input/output SHA-256:
- `docs/yulang-operational-type-safety-ja.tex`: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
- `notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean`: `568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a`
- `notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean`: `02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861`
- `notes/theory/lean/YulangClosure/PaperTypeFormation.lean`: `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`
- `notes/theory/lean/YulangClosure/DeclSubst.lean`: `f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258`
- `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`: `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`
- `notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean`: `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`
- `notes/theory/lean/.lake/R22Audit.lean`: `ff63bb4a3a557699c7a88beca4d26008f7f71039eaa066a6324c4f1ae309182c`

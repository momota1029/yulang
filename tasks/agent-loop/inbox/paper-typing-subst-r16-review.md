# R16.2 independent review — frozen report

Verdict: **NO BLOCKING OR MAJOR FINDINGS** for the assigned raw syntax/declaration mapping prerequisite. This is an independent review of the frozen artifact, not approval of the full paper typing theorem or production behavior.

Reviewer: `/root/r16_independent_review`, assigned by `/root`; no participation in R14–R16 construction, repair, or counterexample work. No children, source repairs, Git operations, Rust execution, external contact, or new semantic authority. Snapshot identifier supplied by primary: `bc6f57eba`, worktree `/tmp/yulang-r16-review`; no Git command was used to re-establish that identifier.

## Inputs and source claim

Read root AGENTS.md and AGENTS.pre-sprint.md; rules/goal-driven-sprints.md; yulang-lean-proofs skill and its sources/execution references; current state/navigation; R16 original and r16.1/r16.2 contracts; producer revision-2 handoff and primary receipt. Those receipts were checked against the actual source and fresh checker output.

Original parent: operational manuscript `docs/yulang-operational-type-safety-ja.tex:203–207,237,953–977`, value-only forall introduction with freshness over the shared declaration/environment context and simultaneous substitution throughout declarations, environments, plans, payload/response and result. Read its opening correction at lines 56 onward: the older raw-resume rule does not establish source-owner correspondence. Also inspected the corrected core note §§1–2 (V1) and corrected-machine simulation §1. These research constructions do not grant semantic adoption.

Fresh SHA-256 checks:

| Input | SHA-256 |
| --- | --- |
| PaperExecutionBinderLaws.lean | 568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a |
| PaperExecutionSyntax.lean | 8789ee5a79b93d6fef2cff1db8692de67f4bc8b290a92ec3e37cac34b0074939 |
| PaperExecutionTypingSubstitution.lean | 30f13a5fbbb11cd5763347efebcc5300e9119884eb4494a41d97bdaeb0731241 |
| PaperTypeSubstitution.lean | 02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861 |
| PaperTypeFormation.lean | 29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13 |
| DeclSubst.lean | f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258 |
| .lake/R16Audit.lean | 905385495f1a0fcdcc76961af2ecf2b365eac72470af6b81a605b7d703530d77 |
| operational manuscript | a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b |
| r16.2 contract | 4a2d37ba591815ce2d824ca62152980b769dffafea2d424b0853ae164236faee |
| worker revision-2 handoff | 77df07e5f7f8cf6dd9e4caf228da857b5c450fe217534faba8d552145478bf39 |
| primary final audit receipt | 3ae2be6d90b80d630cf96f4795aa16df5e72552980e8013b528187391b231046 |

Every explicitly frozen proof dependency matched. No dependency was changed.

## Independent source and proof coverage

All names below are in `YulangClosure.PaperTypes`. Inspected the actual constructors and mappings, not a reduced model.

- `ShiftAt` at BinderLaws:140–167 has exactly the nine required fields: Value, Computation, PatternPlan, ConstructorBranch, GuardedBranch, ValueArm, OperationArm, HandlerPlan, MapperPlan. Each quantifies raw object, its size equality, arbitrary depth, arbitrary substitution. The public projections at :426–469 instantiate `shiftAt_all (sizeOf x)` with `rfl`; no size condition or other hypothesis leaks into their statements.
- `shiftAt_all` at :169–423 uses one `Nat.strongRecOn`. Its actual pinned declaration in installed `Init/WF.lean:246–250` supplies only strictly smaller indices. Each family helper at :172–189 calls that common IH with `sizeOf x < n`. Ordinary constructor cases cover all 20 Value constructors, 26 Computation constructors, 11 PatternPlan constructors, and each of the six singleton families.
- Direct child bounds come from constructor size equations via `simp +arith` and `omega`. Container bounds use `List.sizeOf_lt_of_mem`. Record payload and recursive-binding normalization at :126–137 preserves the concrete label/presence/value and name/value projections; :213–224 and corresponding list branches derive the projected child bounds. Pattern record defaults at :271–274 explicitly split none/some and use the projected size bounds. These are strict bounds for actual recursive children, not a new assumed well-foundedness law.
- `Value.typeAbstraction` at :193–196 unfolds the actual map and applies the Value IH at `depth + 1`. OperationArm at :351–365 destructs the actual `rigidBinders` and guard; its frozen mapper at Syntax:413–421 lifts by that count. `liftSubN_add` normalizes the child substitution to depth plus that count, for payload pattern, optional guard and body. No fixed binder count replaces the stored one.
- Both optional guards (GuardedBranch and OperationArm), optional pattern defaults, prefix/suffix pattern lists, record spread/rest binders, all payload/argument lists, switch branches, recursive bindings, handler value/operation arms, tryArms/waitArm and remaining operation arms are retained. Type application, adapter/view metadata and OperationInstance fields (identity, type arguments, payload, response) use the actual substitution operations.
- `mapTemplateBody_shift_substitution_commutes` at :471–475 uses the actual mapper at Syntax:491–495: identity, arity, every formal, result, and executable Computation body. Body commutation is the computation theorem at depth plus actual type arity; code is not mapped as identity.
- `mapOperationDeclaration_shift_substitution_commutes` at :477–481 applies actual `OperationDeclaration.substAmbient` (Formation:241 onward), retaining identity/arity and mapping both payload/response templates under actual arity. Nominal constructors (:483–487) retain identity/arity and map every payload template. Primitive signatures (:489–493) retain identity/arity and map every argument/result.
- `mapDeclarationTable_shift_substitution_commutes` at :495–504 covers operations, nominalConstructors, primitives, templates and unchanged nativeListIdentity through the actual record map (Syntax:506–541). Equality is of the complete table.
- Public types retain exactly `∀ depth σ x` and the fixed commutation equation; the operation declaration case uses `substAmbient`. No freshness, formation, typing, closedness, finite-depth, or safe-subset hypothesis was added. No existential/shared witness is independently reselected.

Searched the complete direct imported proof cone (BinderLaws, ExecutionSyntax, TypeFormation, TypeSubstitution, DeclSubst) for `sorry`, `admit`, `axiom`, `skipKernelTC`, `native_decide`, `implemented_by`, `unsafe`, and `set_option`: no matches. Actual declarations are theorem declarations. The fresh imported public-theorem axiom audits below also audit their indirect proof dependencies. No assumed LocalLaws or proposition definition is being counted as an instance.

## Fresh checker evidence and resource use

Read pin, lakefile.toml, lake-manifest.json: `leanprover/lean4:v4.35.0`, library YulangClosure, no external packages, per-Lean `-j1 -M1024`. Read-only `elan which lake` exited 0 and resolved the installed native binary below. Installed `include/lean/version.h` reports release `LEAN_VERSION_STRING "4.35.0"`, platform x86_64-unknown-linux-gnu. Version-only invocations were explicitly excluded by the primary's review followup to preserve the call budget; no independent executable --version receipt is claimed.

Both calls were serial, in `/tmp/yulang-r16-review/notes/theory/lean`, with `LEAN_NUM_THREADS=1`, Python subprocess elapsed timers and finite timeouts:

1. `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake build +YulangClosure.PaperExecutionBinderLaws`: **exit 0**, **19.759584587 seconds**. Built all five source modules in the direct dependency cone; final output: `Build completed successfully (6 jobs).` Existing/new unused-variable and unused-simp-argument linter warnings were emitted; no errors or proof holes. This was a real focused source build in the isolated cache, not reliance on the primary's cached result.
2. `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean -j1 -M1024 .lake/R16Audit.lean`: **exit 0**, **0.225878154 seconds**. All 22 check/axiom pairs printed completely; fresh output is preserved below.

Total checker elapsed **19.985462741 seconds**, **2 calls**; within the 90-second and 3-call limits. Primary followup authorized only these two focused checks; no third call was used. Active review elapsed was not separately instrumented, so an exact active-seconds receipt is UNKNOWN; review stopped after this finite inspection/check/report sequence within the allocated turn, without renewing its 600-second cap. No tests, broad/default build, installation, dependency mutation or parallel Lean process. The bundled checker was not used because its fresh scratch output is outside the exact report-only write lease; the existing frozen audit supplied the required manual equivalent without editing it.

All 14 new public laws have **[propext, Quot.sound]**. Among the other eight audited declarations, `liftSubN_add` has **[propext]** and the other seven have **[propext, Quot.sound]**. No sorryAx, project axiom, Classical.choice, native assumption or failed declaration appears. No material failed checker result occurred in this independent review. Worker protocol failures and earlier failed diagnostics remain preserved in the unchanged worker handoff and versioned contracts.

## Parent application and remaining obligation

At depth zero, the table law supplies the equality between substituting `liftSub σ` after shifting the complete declaration table and shifting after substituting `σ`. The nine syntax projections supply corresponding plan equalities; the existing type/graph environment laws and `subst_liftSubN_shift_commutes 0 σ` supply context/result equalities. This removes the raw mapping commutation premise in a future forall-introduction substitution case.

It does **not** supply the typing derivation in the fresh binder context. The first remaining seam is actual six-judgment binder weakening/reindexing and freshness transport over the shared declaration/graph/type environments, followed by the value-only forall rule and its arbitrary-substitution case. Owner: primary proof intake under a new exact packet. Actual `PaperValueTyped` (Syntax:645–702) still has no typeAbstraction introduction constructor. Existing `PaperValueTyped.subst_explicit` in TypingSubstitution:114 is explicitly for partial judgments and cannot close that omitted full-paper case.

No accepted raw syntax constructor is omitted from this R16 law. Full paper typing rules, recursive graph guards, execution safety, inference soundness/termination, original A/B claims, source/native/Rust correspondence and production remain OPEN. No source-qualified counterexample was found; this review grants no compiler/source adoption authority.

## Writes stopped

Only this report was intentionally written. The two authorized checks generated isolated Lake/cache outputs; no scratch Lean file was created or changed. Proof, audit scratch, frozen dependencies and all shared records remained read-only. No Lean/Lake process, children, or continuing task remains. **Reviewer writes STOPPED after freezing this report.**

## Complete fresh import audit

```text
COMMAND /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean -j1 -M1024 .lake/R16Audit.lean
EXIT 0 SECONDS 0.2258781540003838
YulangClosure.PaperTypes.subst_shiftTypeSubstitution : ∀ (ty : YulangClosure.PaperTypes.Ty),
  YulangClosure.PaperTypes.subst YulangClosure.PaperTypes.shiftTypeSubstitution ty =
    YulangClosure.PaperTypes.mapVars Nat.succ ty
'YulangClosure.PaperTypes.subst_shiftTypeSubstitution' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.liftSub_shiftTypeSubstitution_commutes : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty),
  (fun index => YulangClosure.PaperTypes.liftSub σ (index + 1)) = fun index =>
    YulangClosure.PaperTypes.subst YulangClosure.PaperTypes.shiftTypeSubstitution (σ index)
'YulangClosure.PaperTypes.liftSub_shiftTypeSubstitution_commutes' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.compose_liftSub : ∀ (outer inner : Nat → YulangClosure.PaperTypes.Ty),
  YulangClosure.PaperTypes.composeTypeSubstitution (YulangClosure.PaperTypes.liftSub outer)
      (YulangClosure.PaperTypes.liftSub inner) =
    YulangClosure.PaperTypes.liftSub (YulangClosure.PaperTypes.composeTypeSubstitution outer inner)
'YulangClosure.PaperTypes.compose_liftSub' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.liftSubN_shift_compose : ∀ (depth : Nat) (σ : Nat → YulangClosure.PaperTypes.Ty),
  YulangClosure.PaperTypes.composeTypeSubstitution
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.liftSub σ))
      (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) =
    YulangClosure.PaperTypes.composeTypeSubstitution
      (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution)
      (YulangClosure.PaperTypes.liftSubN depth σ)
'YulangClosure.PaperTypes.liftSubN_shift_compose' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.subst_liftSubN_shift_commutes : ∀ (depth : Nat) (σ : Nat → YulangClosure.PaperTypes.Ty)
  (ty : YulangClosure.PaperTypes.Ty),
  YulangClosure.PaperTypes.subst (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.liftSub σ))
      (YulangClosure.PaperTypes.subst
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) ty) =
    YulangClosure.PaperTypes.subst
      (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution)
      (YulangClosure.PaperTypes.subst (YulangClosure.PaperTypes.liftSubN depth σ) ty)
'YulangClosure.PaperTypes.subst_liftSubN_shift_commutes' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.liftSubN_add : ∀ (outerDepth innerDepth : Nat) (σ : Nat → YulangClosure.PaperTypes.Ty),
  YulangClosure.PaperTypes.liftSubN outerDepth (YulangClosure.PaperTypes.liftSubN innerDepth σ) =
    YulangClosure.PaperTypes.liftSubN (innerDepth + outerDepth) σ
'YulangClosure.PaperTypes.liftSubN_add' depends on axioms: [propext]
YulangClosure.PaperTypes.mapTypeEnvironment_shift_substitution_commutes : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  (environment : YulangClosure.PaperTypes.TypeEnvironment),
  YulangClosure.PaperTypes.mapTypeEnvironment (YulangClosure.PaperTypes.liftSub σ)
      (YulangClosure.PaperTypes.mapTypeEnvironment YulangClosure.PaperTypes.shiftTypeSubstitution environment) =
    YulangClosure.PaperTypes.mapTypeEnvironment YulangClosure.PaperTypes.shiftTypeSubstitution
      (YulangClosure.PaperTypes.mapTypeEnvironment σ environment)
'YulangClosure.PaperTypes.mapTypeEnvironment_shift_substitution_commutes' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.mapGraphEnvironment_shift_substitution_commutes : ∀ (σ : Nat → YulangClosure.PaperTypes.Ty)
  (environment : YulangClosure.PaperTypes.GraphEnvironment),
  YulangClosure.PaperTypes.mapGraphEnvironment (YulangClosure.PaperTypes.liftSub σ)
      (YulangClosure.PaperTypes.mapGraphEnvironment YulangClosure.PaperTypes.shiftTypeSubstitution environment) =
    YulangClosure.PaperTypes.mapGraphEnvironment YulangClosure.PaperTypes.shiftTypeSubstitution
      (YulangClosure.PaperTypes.mapGraphEnvironment σ environment)
'YulangClosure.PaperTypes.mapGraphEnvironment_shift_substitution_commutes' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.mapPaperValue_shift_substitution_commutes : ∀ (depth : Nat)
  (σ : Nat → YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.Value),
  YulangClosure.PaperTypes.mapPaperValue (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.liftSub σ))
      (YulangClosure.PaperTypes.mapPaperValue
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    YulangClosure.PaperTypes.mapPaperValue
      (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution)
      (YulangClosure.PaperTypes.mapPaperValue (YulangClosure.PaperTypes.liftSubN depth σ) x)
'YulangClosure.PaperTypes.mapPaperValue_shift_substitution_commutes' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.mapPaperComputation_shift_substitution_commutes : ∀ (depth : Nat)
  (σ : Nat → YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.Computation),
  YulangClosure.PaperTypes.mapPaperComputation
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.liftSub σ))
      (YulangClosure.PaperTypes.mapPaperComputation
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    YulangClosure.PaperTypes.mapPaperComputation
      (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution)
      (YulangClosure.PaperTypes.mapPaperComputation (YulangClosure.PaperTypes.liftSubN depth σ) x)
'YulangClosure.PaperTypes.mapPaperComputation_shift_substitution_commutes' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.mapPaperPattern_shift_substitution_commutes : ∀ (depth : Nat)
  (σ : Nat → YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.PatternPlan),
  YulangClosure.PaperTypes.mapPaperPattern
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.liftSub σ))
      (YulangClosure.PaperTypes.mapPaperPattern
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    YulangClosure.PaperTypes.mapPaperPattern
      (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution)
      (YulangClosure.PaperTypes.mapPaperPattern (YulangClosure.PaperTypes.liftSubN depth σ) x)
'YulangClosure.PaperTypes.mapPaperPattern_shift_substitution_commutes' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.mapConstructorBranch_shift_substitution_commutes : ∀ (depth : Nat)
  (σ : Nat → YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.ConstructorBranch),
  YulangClosure.PaperTypes.mapConstructorBranch
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.liftSub σ))
      (YulangClosure.PaperTypes.mapConstructorBranch
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    YulangClosure.PaperTypes.mapConstructorBranch
      (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution)
      (YulangClosure.PaperTypes.mapConstructorBranch (YulangClosure.PaperTypes.liftSubN depth σ) x)
'YulangClosure.PaperTypes.mapConstructorBranch_shift_substitution_commutes' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.mapGuardedBranch_shift_substitution_commutes : ∀ (depth : Nat)
  (σ : Nat → YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.GuardedBranch),
  YulangClosure.PaperTypes.mapGuardedBranch
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.liftSub σ))
      (YulangClosure.PaperTypes.mapGuardedBranch
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    YulangClosure.PaperTypes.mapGuardedBranch
      (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution)
      (YulangClosure.PaperTypes.mapGuardedBranch (YulangClosure.PaperTypes.liftSubN depth σ) x)
'YulangClosure.PaperTypes.mapGuardedBranch_shift_substitution_commutes' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.mapValueArm_shift_substitution_commutes : ∀ (depth : Nat)
  (σ : Nat → YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.ValueArm),
  YulangClosure.PaperTypes.mapValueArm (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.liftSub σ))
      (YulangClosure.PaperTypes.mapValueArm
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    YulangClosure.PaperTypes.mapValueArm
      (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution)
      (YulangClosure.PaperTypes.mapValueArm (YulangClosure.PaperTypes.liftSubN depth σ) x)
'YulangClosure.PaperTypes.mapValueArm_shift_substitution_commutes' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.mapOperationArm_shift_substitution_commutes : ∀ (depth : Nat)
  (σ : Nat → YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.OperationArm),
  YulangClosure.PaperTypes.mapOperationArm
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.liftSub σ))
      (YulangClosure.PaperTypes.mapOperationArm
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    YulangClosure.PaperTypes.mapOperationArm
      (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution)
      (YulangClosure.PaperTypes.mapOperationArm (YulangClosure.PaperTypes.liftSubN depth σ) x)
'YulangClosure.PaperTypes.mapOperationArm_shift_substitution_commutes' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.mapHandlerPlan_shift_substitution_commutes : ∀ (depth : Nat)
  (σ : Nat → YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.HandlerPlan),
  YulangClosure.PaperTypes.mapHandlerPlan (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.liftSub σ))
      (YulangClosure.PaperTypes.mapHandlerPlan
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    YulangClosure.PaperTypes.mapHandlerPlan
      (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution)
      (YulangClosure.PaperTypes.mapHandlerPlan (YulangClosure.PaperTypes.liftSubN depth σ) x)
'YulangClosure.PaperTypes.mapHandlerPlan_shift_substitution_commutes' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.mapMapperPlan_shift_substitution_commutes : ∀ (depth : Nat)
  (σ : Nat → YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.MapperPlan),
  YulangClosure.PaperTypes.mapMapperPlan (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.liftSub σ))
      (YulangClosure.PaperTypes.mapMapperPlan
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    YulangClosure.PaperTypes.mapMapperPlan
      (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution)
      (YulangClosure.PaperTypes.mapMapperPlan (YulangClosure.PaperTypes.liftSubN depth σ) x)
'YulangClosure.PaperTypes.mapMapperPlan_shift_substitution_commutes' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.mapTemplateBody_shift_substitution_commutes : ∀ (depth : Nat)
  (σ : Nat → YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.TemplateBody),
  YulangClosure.PaperTypes.mapTemplateBody
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.liftSub σ))
      (YulangClosure.PaperTypes.mapTemplateBody
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    YulangClosure.PaperTypes.mapTemplateBody
      (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution)
      (YulangClosure.PaperTypes.mapTemplateBody (YulangClosure.PaperTypes.liftSubN depth σ) x)
'YulangClosure.PaperTypes.mapTemplateBody_shift_substitution_commutes' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.mapOperationDeclaration_shift_substitution_commutes : ∀ (depth : Nat)
  (σ : Nat → YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.OperationDeclaration),
  YulangClosure.PaperTypes.OperationDeclaration.substAmbient
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.liftSub σ))
      (YulangClosure.PaperTypes.OperationDeclaration.substAmbient
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    YulangClosure.PaperTypes.OperationDeclaration.substAmbient
      (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution)
      (YulangClosure.PaperTypes.OperationDeclaration.substAmbient (YulangClosure.PaperTypes.liftSubN depth σ) x)
'YulangClosure.PaperTypes.mapOperationDeclaration_shift_substitution_commutes' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.mapNominalConstructor_shift_substitution_commutes : ∀ (depth : Nat)
  (σ : Nat → YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.NominalConstructor),
  YulangClosure.PaperTypes.mapNominalConstructor
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.liftSub σ))
      (YulangClosure.PaperTypes.mapNominalConstructor
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    YulangClosure.PaperTypes.mapNominalConstructor
      (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution)
      (YulangClosure.PaperTypes.mapNominalConstructor (YulangClosure.PaperTypes.liftSubN depth σ) x)
'YulangClosure.PaperTypes.mapNominalConstructor_shift_substitution_commutes' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.mapPrimitiveSignature_shift_substitution_commutes : ∀ (depth : Nat)
  (σ : Nat → YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.PrimitiveSignature),
  YulangClosure.PaperTypes.mapPrimitiveSignature
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.liftSub σ))
      (YulangClosure.PaperTypes.mapPrimitiveSignature
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    YulangClosure.PaperTypes.mapPrimitiveSignature
      (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution)
      (YulangClosure.PaperTypes.mapPrimitiveSignature (YulangClosure.PaperTypes.liftSubN depth σ) x)
'YulangClosure.PaperTypes.mapPrimitiveSignature_shift_substitution_commutes' depends on axioms: [propext, Quot.sound]
YulangClosure.PaperTypes.mapDeclarationTable_shift_substitution_commutes : ∀ (depth : Nat)
  (σ : Nat → YulangClosure.PaperTypes.Ty) (declarations : YulangClosure.PaperTypes.DeclarationTable),
  YulangClosure.PaperTypes.mapDeclarationTable
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.liftSub σ))
      (YulangClosure.PaperTypes.mapDeclarationTable
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) declarations) =
    YulangClosure.PaperTypes.mapDeclarationTable
      (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution)
      (YulangClosure.PaperTypes.mapDeclarationTable (YulangClosure.PaperTypes.liftSubN depth σ) declarations)
'YulangClosure.PaperTypes.mapDeclarationTable_shift_substitution_commutes' depends on axioms: [propext, Quot.sound]
```

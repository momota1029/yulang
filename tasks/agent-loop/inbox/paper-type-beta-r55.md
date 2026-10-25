# R55 frozen leaf handoff — strict audit failed

Worker `/root/r55_type_beta_finalize`, registered lean_prover leaf; isolated checkout `/tmp/yulang-r55-type-beta-finalize`. Baseline `7ea6d0130f4258e0eedf43643130da590a7b0d45` verified by reading the worktree HEAD (no Git command). No descendants, compiler changes, tests, root imports, dependency/configuration changes, network work, Git commands or other-worker writes. Shared primary contract was read only because it postdates the isolated baseline.

## Status and exact residual

CONSTRUCTED AND MODULE-BUILD ACCEPTED; COMPLETE STRICT AUDIT FAILED; INDEPENDENT REVIEW NOT RUN; SOURCE/NATIVE AND PRODUCTION OPEN. This packet did not succeed. No retry or second construction attempt.

One exact proof line was added after the existing attachment simplification in `cancelAt_all`, PatternPlan.record case (line 214): `exact List.attach_map_subtype_val fields`. The list goal is `List.map Subtype.val fields.attach = fields`; pinned Init/Data/List/Attach.lean:154 provides that equation. No statements, hypotheses, quantifiers, constructors or definitions changed.

Candidate SHA-256 `0a1834040a0201c0c472f66138f6501094f7138dd3614f2bc4439a8be0cda1c8`; frozen R54 seed SHA-256 `4c7b71c5387bf8d078925b8734fd0afb66b97dc2e58aa1026e96b4ff526e7359`.

The native module build exited 0. The unchanged pinned audit template exited 1: its eight `_private.YulangClosure.PaperTypeBetaExecution.0...` identifiers are written as raw dotted Lean identifiers; Lean reports `unexpected identifier after decimal point; consider parenthesizing the number` at `.lake/R55Audit.lean:33:77`, followed by unknown-identifier/field-notation parser diagnostics. Twenty-six public declaration blocks completed; eight private blocks did not. This is an audit-template execution obstruction, not a reported mathematical counterexample. All four calls were consumed; no audit correction/check is authorized in this packet. First remaining evidence owner: primary, to authorize a separate corrected exact-name audit packet and fresh independent review. All parent gates remain OPEN.

## Source and application to original parent

Original paper: `docs/yulang-operational-type-safety-ja.tex`, execution-type section and one-step preservation proof at line 1101 (type application uses simultaneous type substitution), universal abstraction/application at 2063–2065. Read its opening source-correspondence correction/research status. Current corrected candidate account: `notes/theory/2026-10-24-corrected-core-value-continuation.md`, §2 V1(b), same substitution across environments, declaration instances, payload/response, result and body. These research manuscripts are locators/claims, not new semantic adoption authority.

Exact existing definitions read: `YulangClosure.PaperTypes.Ty`, `PaperValueTyped.typeAbstraction`, `PaperValueTyped.typeApplication`, `PaperValueTyped.subst_explicit`, `mapPaperValue`, `mapPaperComputation`, `PatternPlan.record`, `TemplateBody`, `PaperCoreStep.step`; candidate namespace `YulangClosure.PaperTypes.PaperTypeBetaExecution`.

Parent application in the built candidate: `instantiate_body` applies `YulangClosure.PaperTypes.PaperValueTyped.subst_explicit (instantiateSubstitution [argument])` to the abstraction body, then cancellation restores the same arbitrary shared declaration/graph/term contexts d/g/e. `typeBetaValue_applicable` inverts existing type application/abstraction rules; `typeBetaValue_preservation` transports the actual redex result; `typeBetaForce_preservation` lifts only that administrative beta step. `force_typeBeta_delay` then uses the existing `PaperCoreStep.preservation` for a separate Force/Delay step, retaining a typing judgment at the intermediate endpoint. Body, argument and result type remain distinct; no closed-context premise was added.

Represented: cancellation over every constructor of the existing mutually recursive raw Value/Computation/PatternPlan/branch/arm/handler/mapper syntax, records with optional defaults/spread, reference/equality patterns, rigid operation binders, shared contexts, nested forall and mu, formal-binder template bodies, declarations, operation instances and metadata type fields. This covers the represented value type-beta redex and its Force context only. Omitted/unestablished: completeness/source realization of these raw representations and judgments; source/native correspondence; full machine/executor preservation and observations/effect/lifetime contracts; initial source elaboration; Simple-sub A/B; production authority. The source-wide one-step preservation theorem remains the original open parent at its respective source/executor owners; no claim of full-language closure follows from this local build.

## Pins and environment

All listed pins matched before the first write. Contract SHA-256 `611ea5ec46a32be40d4a45fe46257c8686f868429eeb25f4525a79cea0ebaeb1` (shared read-only path `/home/momota1029/rust/yulang/tasks/agent-loop/sprints/paper-type-beta-execution-r55.md`).

```json
{
  "notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean": "568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a",
  "notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean": "3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41",
  "notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean": "02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861",
  "notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean": "e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932",
  "notes/theory/lean/YulangClosure/PaperTermSubstitution.lean": "a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f",
  "notes/theory/lean/YulangClosure/DeclSubst.lean": "f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258",
  "notes/theory/lean/YulangClosure/PaperPerformLetExecution.lean": "2f0026049554cb870158115b4bab8d42f7cbee8b030ee3f84a904763c328cac0",
  "notes/theory/lean/lean-toolchain": "ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c",
  "notes/theory/lean/lakefile.toml": "2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194",
  "notes/theory/lean/lake-manifest.json": "058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3",
  "docs/yulang-operational-type-safety-ja.tex": "a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b",
  "notes/theory/2026-10-24-corrected-core-value-continuation.md": "4d8ffd63cbb65cd6917145fa31a4cb3f04656a19f7b71fd0e3fdd6cecaabfbeb",
  "notes/theory/lean/.lake/R55Audit.lean": "72110febc4d315a0aecd77ab4e862e2cf03ac9eacf8d8f4d7872850a6f4f2541",
  "/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Init/Data/List/Attach.lean": "2d392f48cdd9c7886817d3ced7ea82b447e25738ca4249f97492ced94e8baf38"
}
```

Native Lake resolved by exact installed distribution path `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`; SHA-256 `8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1`. Lake 5.0.0-src+eb6cafb (Lean 4.35.0). Lean 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release. Pinned lakefile supplies `-j1 -M1024`; environment `LEAN_NUM_THREADS=1`, `LAKE_JOBS=1`, native bin prepended to PATH. No installation/dependency mutation.

## Literal native receipts

All cwd values are `/tmp/yulang-r55-type-beta-finalize/notes/theory/lean`. Complete exact argv/cwd/exit/timings/stdout/stderr hashes are preserved in each `.lake/R55-call-01..04.json`; separate complete stdout/stderr siblings are immutable. No extra Lean checker/helper was run: the fixed four-call manual audit template provides declaration-kind and axiom checks, though its private-name syntax failed.

| Call | Native argv suffix | Exit | Seconds |
| --- | --- | --- | --- |
| 1 | `--version` | 0 | 0.438276772 |
| 2 | `env lean --version` | 0 | 0.074728788 |
| 3 | `build +YulangClosure.PaperTypeBetaExecution` | 0 | 31.556839210 |
| 4 | `env lean -j1 -M1024 .lake/R55Audit.lean` | 1 | 2.719123593 |

Total native time 34.788968363 seconds / 90; 4 calls / 4. No timeout. Candidate build failure artifact absent because build succeeded. All native processes reaped; Python runner exited 1 on strict audit failure.

Worker pre-read origin capture was missed (UNKNOWN/receipt defect); no origin is fabricated. The primary acknowledged charging all worker elapsed conservatively from the earlier contract monotonic origin `47855273027957 ns`. That conservative charge is recorded in R55-origin.json and R55-stop.json. No effective model/effort/runtime identity beyond the actual assigned worker is certified here.

## Actual declaration audit

All 26 completed public declarations were checked as theorem declarations. Their full actual printed types and complete `#print axioms` results, together with every parser failure, are copied verbatim below. Twenty-four public declarations report `[propext, Quot.sound]`; `nested_poly_mu` and `shared_variable_countercase` report no axioms. No standard-axiom-free claim applies to the other 24. Eight private declarations have NO successful individual printed-type/axiom receipt in this run:

- `_private.YulangClosure.PaperTypeBetaExecution.0.YulangClosure.PaperTypes.PaperTypeBetaExecution.map_eq_self_iff`
- `_private.YulangClosure.PaperTypeBetaExecution.0.YulangClosure.PaperTypes.PaperTypeBetaExecution.map_attach_eq_iff`
- `_private.YulangClosure.PaperTypeBetaExecution.0.YulangClosure.PaperTypes.PaperTypeBetaExecution.mapAdapterMetadata_cancel`
- `_private.YulangClosure.PaperTypeBetaExecution.0.YulangClosure.PaperTypes.PaperTypeBetaExecution.mapViewMetadata_cancel`
- `_private.YulangClosure.PaperTypeBetaExecution.0.YulangClosure.PaperTypes.PaperTypeBetaExecution.mapOperationInstance_cancel`
- `_private.YulangClosure.PaperTypeBetaExecution.0.YulangClosure.PaperTypes.PaperTypeBetaExecution.mapPaperValue_record_eq`
- `_private.YulangClosure.PaperTypeBetaExecution.0.YulangClosure.PaperTypes.PaperTypeBetaExecution.mapPaperComputation_recursive_eq`
- `_private.YulangClosure.PaperTypeBetaExecution.0.YulangClosure.PaperTypes.PaperTypeBetaExecution.cancelAt_all`

```text
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.liftSubN_cancel
YulangClosure.PaperTypes.PaperTypeBetaExecution.liftSubN_cancel : ∀ (depth : Nat)
  (argument : YulangClosure.PaperTypes.Ty),
  YulangClosure.PaperTypes.composeTypeSubstitution
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.instantiateSubstitution [argument]))
      (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) =
    YulangClosure.PaperTypes.idSub
'YulangClosure.PaperTypes.PaperTypeBetaExecution.liftSubN_cancel' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.liftSubN_cancel
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.subst_liftSubN_cancel
YulangClosure.PaperTypes.PaperTypeBetaExecution.subst_liftSubN_cancel : ∀ (depth : Nat)
  (argument ty : YulangClosure.PaperTypes.Ty),
  YulangClosure.PaperTypes.subst
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.instantiateSubstitution [argument]))
      (YulangClosure.PaperTypes.subst
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) ty) =
    ty
'YulangClosure.PaperTypes.PaperTypeBetaExecution.subst_liftSubN_cancel' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.subst_liftSubN_cancel
.lake/R55Audit.lean:33:77: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:37:8: error(lean.unknownIdentifier): Unknown identifier `_private.YulangClosure.PaperTypeBetaExecution`
.lake/R55Audit.lean:37:53: error: Invalid field notation: Identifier or numeral expected
.lake/R55Audit.lean:37:54: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:38:14: error(lean.unknownIdentifier): Unknown constant `_private.YulangClosure.PaperTypeBetaExecution`
.lake/R55Audit.lean:38:59: error: unexpected token '.'; expected command
.lake/R55Audit.lean:40:80: error: Invalid field notation: Identifier or numeral expected
.lake/R55Audit.lean:40:81: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:46:77: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:50:8: error(lean.unknownIdentifier): Unknown identifier `_private.YulangClosure.PaperTypeBetaExecution`
.lake/R55Audit.lean:50:53: error: Invalid field notation: Identifier or numeral expected
.lake/R55Audit.lean:50:54: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:51:14: error(lean.unknownIdentifier): Unknown constant `_private.YulangClosure.PaperTypeBetaExecution`
.lake/R55Audit.lean:51:59: error: unexpected token '.'; expected command
.lake/R55Audit.lean:53:80: error: Invalid field notation: Identifier or numeral expected
.lake/R55Audit.lean:53:81: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:59:77: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:63:8: error(lean.unknownIdentifier): Unknown identifier `_private.YulangClosure.PaperTypeBetaExecution`
.lake/R55Audit.lean:63:53: error: Invalid field notation: Identifier or numeral expected
.lake/R55Audit.lean:63:54: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:64:14: error(lean.unknownIdentifier): Unknown constant `_private.YulangClosure.PaperTypeBetaExecution`
.lake/R55Audit.lean:64:59: error: unexpected token '.'; expected command
.lake/R55Audit.lean:66:80: error: Invalid field notation: Identifier or numeral expected
.lake/R55Audit.lean:66:81: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:72:77: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:76:8: error(lean.unknownIdentifier): Unknown identifier `_private.YulangClosure.PaperTypeBetaExecution`
.lake/R55Audit.lean:76:53: error: Invalid field notation: Identifier or numeral expected
.lake/R55Audit.lean:76:54: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:77:14: error(lean.unknownIdentifier): Unknown constant `_private.YulangClosure.PaperTypeBetaExecution`
.lake/R55Audit.lean:77:59: error: unexpected token '.'; expected command
.lake/R55Audit.lean:79:80: error: Invalid field notation: Identifier or numeral expected
.lake/R55Audit.lean:79:81: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:85:77: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:89:8: error(lean.unknownIdentifier): Unknown identifier `_private.YulangClosure.PaperTypeBetaExecution`
.lake/R55Audit.lean:89:53: error: Invalid field notation: Identifier or numeral expected
.lake/R55Audit.lean:89:54: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:90:14: error(lean.unknownIdentifier): Unknown constant `_private.YulangClosure.PaperTypeBetaExecution`
.lake/R55Audit.lean:90:59: error: unexpected token '.'; expected command
.lake/R55Audit.lean:92:80: error: Invalid field notation: Identifier or numeral expected
.lake/R55Audit.lean:92:81: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:98:77: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:102:8: error(lean.unknownIdentifier): Unknown identifier `_private.YulangClosure.PaperTypeBetaExecution`
.lake/R55Audit.lean:102:53: error: Invalid field notation: Identifier or numeral expected
.lake/R55Audit.lean:102:54: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:103:14: error(lean.unknownIdentifier): Unknown constant `_private.YulangClosure.PaperTypeBetaExecution`
.lake/R55Audit.lean:103:59: error: unexpected token '.'; expected command
.lake/R55Audit.lean:105:80: error: Invalid field notation: Identifier or numeral expected
.lake/R55Audit.lean:105:81: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:111:77: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:115:8: error(lean.unknownIdentifier): Unknown identifier `_private.YulangClosure.PaperTypeBetaExecution`
.lake/R55Audit.lean:115:53: error: Invalid field notation: Identifier or numeral expected
.lake/R55Audit.lean:115:54: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:116:14: error(lean.unknownIdentifier): Unknown constant `_private.YulangClosure.PaperTypeBetaExecution`
.lake/R55Audit.lean:116:59: error: unexpected token '.'; expected command
.lake/R55Audit.lean:118:80: error: Invalid field notation: Identifier or numeral expected
.lake/R55Audit.lean:118:81: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:124:77: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:128:8: error(lean.unknownIdentifier): Unknown identifier `_private.YulangClosure.PaperTypeBetaExecution`
.lake/R55Audit.lean:128:53: error: Invalid field notation: Identifier or numeral expected
.lake/R55Audit.lean:128:54: error: unexpected identifier after decimal point; consider parenthesizing the number
.lake/R55Audit.lean:129:14: error(lean.unknownIdentifier): Unknown constant `_private.YulangClosure.PaperTypeBetaExecution`
.lake/R55Audit.lean:129:59: error: unexpected token '.'; expected command
.lake/R55Audit.lean:131:80: error: Invalid field notation: Identifier or numeral expected
.lake/R55Audit.lean:131:81: error: unexpected identifier after decimal point; consider parenthesizing the number
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.mapPaperValue_cancel
YulangClosure.PaperTypes.PaperTypeBetaExecution.mapPaperValue_cancel : ∀ (depth : Nat)
  (argument : YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.Value),
  YulangClosure.PaperTypes.mapPaperValue
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.instantiateSubstitution [argument]))
      (YulangClosure.PaperTypes.mapPaperValue
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    x
'YulangClosure.PaperTypes.PaperTypeBetaExecution.mapPaperValue_cancel' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.mapPaperValue_cancel
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.mapPaperComputation_cancel
YulangClosure.PaperTypes.PaperTypeBetaExecution.mapPaperComputation_cancel : ∀ (depth : Nat)
  (argument : YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.Computation),
  YulangClosure.PaperTypes.mapPaperComputation
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.instantiateSubstitution [argument]))
      (YulangClosure.PaperTypes.mapPaperComputation
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    x
'YulangClosure.PaperTypes.PaperTypeBetaExecution.mapPaperComputation_cancel' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.mapPaperComputation_cancel
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.mapPaperPattern_cancel
YulangClosure.PaperTypes.PaperTypeBetaExecution.mapPaperPattern_cancel : ∀ (depth : Nat)
  (argument : YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.PatternPlan),
  YulangClosure.PaperTypes.mapPaperPattern
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.instantiateSubstitution [argument]))
      (YulangClosure.PaperTypes.mapPaperPattern
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    x
'YulangClosure.PaperTypes.PaperTypeBetaExecution.mapPaperPattern_cancel' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.mapPaperPattern_cancel
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.mapConstructorBranch_cancel
YulangClosure.PaperTypes.PaperTypeBetaExecution.mapConstructorBranch_cancel : ∀ (depth : Nat)
  (argument : YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.ConstructorBranch),
  YulangClosure.PaperTypes.mapConstructorBranch
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.instantiateSubstitution [argument]))
      (YulangClosure.PaperTypes.mapConstructorBranch
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    x
'YulangClosure.PaperTypes.PaperTypeBetaExecution.mapConstructorBranch_cancel' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.mapConstructorBranch_cancel
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.mapGuardedBranch_cancel
YulangClosure.PaperTypes.PaperTypeBetaExecution.mapGuardedBranch_cancel : ∀ (depth : Nat)
  (argument : YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.GuardedBranch),
  YulangClosure.PaperTypes.mapGuardedBranch
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.instantiateSubstitution [argument]))
      (YulangClosure.PaperTypes.mapGuardedBranch
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    x
'YulangClosure.PaperTypes.PaperTypeBetaExecution.mapGuardedBranch_cancel' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.mapGuardedBranch_cancel
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.mapValueArm_cancel
YulangClosure.PaperTypes.PaperTypeBetaExecution.mapValueArm_cancel : ∀ (depth : Nat)
  (argument : YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.ValueArm),
  YulangClosure.PaperTypes.mapValueArm
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.instantiateSubstitution [argument]))
      (YulangClosure.PaperTypes.mapValueArm
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    x
'YulangClosure.PaperTypes.PaperTypeBetaExecution.mapValueArm_cancel' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.mapValueArm_cancel
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.mapOperationArm_cancel
YulangClosure.PaperTypes.PaperTypeBetaExecution.mapOperationArm_cancel : ∀ (depth : Nat)
  (argument : YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.OperationArm),
  YulangClosure.PaperTypes.mapOperationArm
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.instantiateSubstitution [argument]))
      (YulangClosure.PaperTypes.mapOperationArm
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    x
'YulangClosure.PaperTypes.PaperTypeBetaExecution.mapOperationArm_cancel' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.mapOperationArm_cancel
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.mapHandlerPlan_cancel
YulangClosure.PaperTypes.PaperTypeBetaExecution.mapHandlerPlan_cancel : ∀ (depth : Nat)
  (argument : YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.HandlerPlan),
  YulangClosure.PaperTypes.mapHandlerPlan
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.instantiateSubstitution [argument]))
      (YulangClosure.PaperTypes.mapHandlerPlan
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    x
'YulangClosure.PaperTypes.PaperTypeBetaExecution.mapHandlerPlan_cancel' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.mapHandlerPlan_cancel
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.mapMapperPlan_cancel
YulangClosure.PaperTypes.PaperTypeBetaExecution.mapMapperPlan_cancel : ∀ (depth : Nat)
  (argument : YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.MapperPlan),
  YulangClosure.PaperTypes.mapMapperPlan
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.instantiateSubstitution [argument]))
      (YulangClosure.PaperTypes.mapMapperPlan
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    x
'YulangClosure.PaperTypes.PaperTypeBetaExecution.mapMapperPlan_cancel' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.mapMapperPlan_cancel
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.mapTemplateBody_cancel
YulangClosure.PaperTypes.PaperTypeBetaExecution.mapTemplateBody_cancel : ∀ (depth : Nat)
  (argument : YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.TemplateBody),
  YulangClosure.PaperTypes.mapTemplateBody
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.instantiateSubstitution [argument]))
      (YulangClosure.PaperTypes.mapTemplateBody
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    x
'YulangClosure.PaperTypes.PaperTypeBetaExecution.mapTemplateBody_cancel' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.mapTemplateBody_cancel
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.OperationDeclaration_substAmbient_cancel
YulangClosure.PaperTypes.PaperTypeBetaExecution.OperationDeclaration_substAmbient_cancel : ∀ (depth : Nat)
  (argument : YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.OperationDeclaration),
  YulangClosure.PaperTypes.OperationDeclaration.substAmbient
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.instantiateSubstitution [argument]))
      (YulangClosure.PaperTypes.OperationDeclaration.substAmbient
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    x
'YulangClosure.PaperTypes.PaperTypeBetaExecution.OperationDeclaration_substAmbient_cancel' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.OperationDeclaration_substAmbient_cancel
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.mapNominalConstructor_cancel
YulangClosure.PaperTypes.PaperTypeBetaExecution.mapNominalConstructor_cancel : ∀ (depth : Nat)
  (argument : YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.NominalConstructor),
  YulangClosure.PaperTypes.mapNominalConstructor
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.instantiateSubstitution [argument]))
      (YulangClosure.PaperTypes.mapNominalConstructor
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    x
'YulangClosure.PaperTypes.PaperTypeBetaExecution.mapNominalConstructor_cancel' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.mapNominalConstructor_cancel
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.mapPrimitiveSignature_cancel
YulangClosure.PaperTypes.PaperTypeBetaExecution.mapPrimitiveSignature_cancel : ∀ (depth : Nat)
  (argument : YulangClosure.PaperTypes.Ty) (x : YulangClosure.PaperTypes.PrimitiveSignature),
  YulangClosure.PaperTypes.mapPrimitiveSignature
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.instantiateSubstitution [argument]))
      (YulangClosure.PaperTypes.mapPrimitiveSignature
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) x) =
    x
'YulangClosure.PaperTypes.PaperTypeBetaExecution.mapPrimitiveSignature_cancel' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.mapPrimitiveSignature_cancel
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.mapDeclarationTable_cancel
YulangClosure.PaperTypes.PaperTypeBetaExecution.mapDeclarationTable_cancel : ∀ (depth : Nat)
  (argument : YulangClosure.PaperTypes.Ty) (d : YulangClosure.PaperTypes.DeclarationTable),
  YulangClosure.PaperTypes.mapDeclarationTable
      (YulangClosure.PaperTypes.liftSubN depth (YulangClosure.PaperTypes.instantiateSubstitution [argument]))
      (YulangClosure.PaperTypes.mapDeclarationTable
        (YulangClosure.PaperTypes.liftSubN depth YulangClosure.PaperTypes.shiftTypeSubstitution) d) =
    d
'YulangClosure.PaperTypes.PaperTypeBetaExecution.mapDeclarationTable_cancel' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.mapDeclarationTable_cancel
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.mapTypeEnvironment_cancel
YulangClosure.PaperTypes.PaperTypeBetaExecution.mapTypeEnvironment_cancel : ∀ (argument : YulangClosure.PaperTypes.Ty)
  (e : YulangClosure.PaperTypes.TypeEnvironment),
  YulangClosure.PaperTypes.mapTypeEnvironment (YulangClosure.PaperTypes.instantiateSubstitution [argument])
      (YulangClosure.PaperTypes.mapTypeEnvironment YulangClosure.PaperTypes.shiftTypeSubstitution e) =
    e
'YulangClosure.PaperTypes.PaperTypeBetaExecution.mapTypeEnvironment_cancel' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.mapTypeEnvironment_cancel
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.mapGraphEnvironment_cancel
YulangClosure.PaperTypes.PaperTypeBetaExecution.mapGraphEnvironment_cancel : ∀ (argument : YulangClosure.PaperTypes.Ty)
  (g : YulangClosure.PaperTypes.GraphEnvironment),
  YulangClosure.PaperTypes.mapGraphEnvironment (YulangClosure.PaperTypes.instantiateSubstitution [argument])
      (YulangClosure.PaperTypes.mapGraphEnvironment YulangClosure.PaperTypes.shiftTypeSubstitution g) =
    g
'YulangClosure.PaperTypes.PaperTypeBetaExecution.mapGraphEnvironment_cancel' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.mapGraphEnvironment_cancel
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaValue_shape
YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaValue_shape : ∀ (body : YulangClosure.PaperTypes.Value)
  (argument : YulangClosure.PaperTypes.Ty),
  YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaValue (body.typeAbstraction.typeApplication argument) =
    Option.some
      (YulangClosure.PaperTypes.mapPaperValue (YulangClosure.PaperTypes.instantiateSubstitution [argument]) body)
'YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaValue_shape' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaValue_shape
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.instantiate_body
@YulangClosure.PaperTypes.PaperTypeBetaExecution.instantiate_body : ∀ {d : YulangClosure.PaperTypes.DeclarationTable}
  {g : YulangClosure.PaperTypes.GraphEnvironment} {e : YulangClosure.PaperTypes.TypeEnvironment}
  {body : YulangClosure.PaperTypes.Value} {bodyType : YulangClosure.PaperTypes.Ty}
  (argument : YulangClosure.PaperTypes.Ty),
  YulangClosure.PaperTypes.PaperValueTyped
      (YulangClosure.PaperTypes.mapDeclarationTable YulangClosure.PaperTypes.shiftTypeSubstitution d)
      (YulangClosure.PaperTypes.mapGraphEnvironment YulangClosure.PaperTypes.shiftTypeSubstitution g)
      (YulangClosure.PaperTypes.mapTypeEnvironment YulangClosure.PaperTypes.shiftTypeSubstitution e) body bodyType →
    YulangClosure.PaperTypes.PaperValueTyped d g e
      (YulangClosure.PaperTypes.mapPaperValue (YulangClosure.PaperTypes.instantiateSubstitution [argument]) body)
      (YulangClosure.PaperTypes.instantiateType [argument] bodyType)
'YulangClosure.PaperTypes.PaperTypeBetaExecution.instantiate_body' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.instantiate_body
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaValue_applicable
@YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaValue_applicable : ∀
  {d : YulangClosure.PaperTypes.DeclarationTable} {g : YulangClosure.PaperTypes.GraphEnvironment}
  {e : YulangClosure.PaperTypes.TypeEnvironment} {body : YulangClosure.PaperTypes.Value}
  {argument resultType : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperValueTyped d g e (body.typeAbstraction.typeApplication argument) resultType →
    YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaValue (body.typeAbstraction.typeApplication argument) =
        Option.some
          (YulangClosure.PaperTypes.mapPaperValue (YulangClosure.PaperTypes.instantiateSubstitution [argument]) body) ∧
      YulangClosure.PaperTypes.PaperValueTyped d g e
        (YulangClosure.PaperTypes.mapPaperValue (YulangClosure.PaperTypes.instantiateSubstitution [argument]) body)
        resultType
'YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaValue_applicable' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaValue_applicable
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaValue_preservation
@YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaValue_preservation : ∀
  {d : YulangClosure.PaperTypes.DeclarationTable} {g : YulangClosure.PaperTypes.GraphEnvironment}
  {e : YulangClosure.PaperTypes.TypeEnvironment} {value next : YulangClosure.PaperTypes.Value}
  {resultType : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperValueTyped d g e value resultType →
    YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaValue value = Option.some next →
      YulangClosure.PaperTypes.PaperValueTyped d g e next resultType
'YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaValue_preservation' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaValue_preservation
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaForce_preservation
@YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaForce_preservation : ∀
  {d : YulangClosure.PaperTypes.DeclarationTable} {g : YulangClosure.PaperTypes.GraphEnvironment}
  {e : YulangClosure.PaperTypes.TypeEnvironment} {source next : YulangClosure.PaperTypes.Computation}
  {resultType : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperComputationTyped d g e source resultType →
    YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaForce source = Option.some next →
      YulangClosure.PaperTypes.PaperComputationTyped d g e next resultType
'YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaForce_preservation' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaForce_preservation
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.force_typeBeta_delay
@YulangClosure.PaperTypes.PaperTypeBetaExecution.force_typeBeta_delay : ∀
  {d : YulangClosure.PaperTypes.DeclarationTable} {g : YulangClosure.PaperTypes.GraphEnvironment}
  {e : YulangClosure.PaperTypes.TypeEnvironment} {body : YulangClosure.PaperTypes.Computation}
  {argument resultType : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperComputationTyped d g e
      (YulangClosure.PaperTypes.Computation.force
        ((YulangClosure.PaperTypes.Value.delay body).typeAbstraction.typeApplication argument))
      resultType →
    have body' :=
      YulangClosure.PaperTypes.mapPaperComputation (YulangClosure.PaperTypes.instantiateSubstitution [argument]) body;
    YulangClosure.PaperTypes.PaperTypeBetaExecution.typeBetaForce
          (YulangClosure.PaperTypes.Computation.force
            ((YulangClosure.PaperTypes.Value.delay body).typeAbstraction.typeApplication argument)) =
        Option.some (YulangClosure.PaperTypes.Computation.force (YulangClosure.PaperTypes.Value.delay body')) ∧
      YulangClosure.PaperTypes.PaperComputationTyped d g e
          (YulangClosure.PaperTypes.Computation.force (YulangClosure.PaperTypes.Value.delay body')) resultType ∧
        YulangClosure.PaperTypes.PaperCoreStep.step
              (YulangClosure.PaperTypes.Computation.force (YulangClosure.PaperTypes.Value.delay body')) =
            Option.some body' ∧
          YulangClosure.PaperTypes.PaperComputationTyped d g e body' resultType
'YulangClosure.PaperTypes.PaperTypeBetaExecution.force_typeBeta_delay' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.force_typeBeta_delay
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.nested_poly_mu
YulangClosure.PaperTypes.PaperTypeBetaExecution.nested_poly_mu : ∀ (argument : YulangClosure.PaperTypes.Ty),
  YulangClosure.PaperTypes.instantiateType [argument]
      ((YulangClosure.PaperTypes.Ty.var 2).callable (YulangClosure.PaperTypes.Ty.var 0)).mu.poly =
    ((YulangClosure.PaperTypes.mapVars Nat.succ (YulangClosure.PaperTypes.mapVars Nat.succ argument)).callable
          (YulangClosure.PaperTypes.Ty.var 0)).mu.poly
'YulangClosure.PaperTypes.PaperTypeBetaExecution.nested_poly_mu' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.nested_poly_mu
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperTypeBetaExecution.shared_variable_countercase
YulangClosure.PaperTypes.PaperTypeBetaExecution.shared_variable_countercase : ∀
  (argument : YulangClosure.PaperTypes.Ty),
  YulangClosure.PaperTypes.instantiateType [argument] (YulangClosure.PaperTypes.Ty.var 3).mu.poly =
    (YulangClosure.PaperTypes.Ty.var 2).mu.poly
'YulangClosure.PaperTypes.PaperTypeBetaExecution.shared_variable_countercase' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperTypeBetaExecution.shared_variable_countercase
```

## Outputs, cache and cessation

Only leased semantic output `notes/theory/lean/YulangClosure/PaperTypeBetaExecution.lean` changed. Leased scratch/receipts: `.lake/R55run.py`, `.lake/R55-origin.json`, `.lake/R55-stop.json`, `.lake/R55-artifacts.json`, `.lake/R55-call-01..04.json` and complete sibling stdout/stderr. Existing pinned `.lake/R55Audit.lean` remained byte-identical. Build/config outputs are confined to worker-owned isolated `.lake/build` and `.lake/config`; primary verification uses a distinct cache. Artifact inventory includes full owned cache hashes, without claiming all inventoried files were newly written.

Artifact inventory SHA-256 `bd7237c0a4f0441a45f53e03cea7e0339a1fced26ece24f52792e65c810a8052`; stop receipt SHA-256 `918cdc7660a661b59cd80032281c90de3b816028215d0a5fb54a9fc11b14c8f0`. The single handoff is this file; its final hash is returned externally to avoid self-reference. Construction/checker writes are stopped; final inventory/handoff freeze is the last filesystem operation before this finishing Python process exits. No background process or descendant remains. No independent self-certification or gate promotion. Primary owns any further packet, review, integration and status updates.

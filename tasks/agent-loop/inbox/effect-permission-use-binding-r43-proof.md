# R43 proof handoff — frozen, writes stopped

Author/runtime identity: `/root/r43_proof`; requested role `lean_prover`, requested effort high; effective model/effort metadata UNKNOWN. Claim class: conditional finite binding mathematics. Independent review NOT RUN by this author. Production and original parent gates OPEN.

## Original source and preserved claim

Governing specification: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1, 1.1–1.2, 3–4. §1.1 preserves both annotated callback and computation arguments, and admits compatible `[signal, write]` inflow while permission covers only `signal`. §1.2/approved `annotation-declared-envelope-a1` correction distinguishes permission, actual inflow and residual; symbolic dependencies stay connected and ordinary constraint generation/propagation supplies inflow. §6 explicitly retracts its old callback result; that result was not used. Top-level inference principles §1 preserve ordinary generation, levels, extrusion/intrusion and the existing hygiene proofs.

Parent claim remains source-wide annotation-effect permission/inflow/subtraction with the original accepted language and source-scoped shared witnesses. This finite package proves only binding/identity and exact payload transport; it does not restrict the parent to computation formals or finite numeric examples. Callback/nested Function permissions, general source forms, provider arrival, correlated Function semantics, actual consumer/Catch/subtraction and whole-language soundness/principality/termination remain outside this model and OPEN. R39's empty/variable-only branch remains accepted with no permission; no such case is reclassified as an error by the original inference. A binder call with no retained permission returns none.

Actual declarations inspected: `YulangClosure.ComputationPermissionEntryR39.Permission`, `Valid`, `prepare`, `permissionFor`, `exact_row_retained`; `YulangClosure.LambdaArgumentEffectIncidenceR41.Label`, `capture`, `freshen`, `entry_to_exact_use`; `YulangClosure.NativeIncidenceAdapterR42.Matches`, `extract`, `accepted_r41_image`, `constructed_entry_to_native`. `YulangClosure.SourceProblem.InferenceSoundness` is a proposition definition, and `YulangClosure.LocalLaws` contains assumed obligations; neither was used as a concrete closure theorem. `OriginalEffectHygiene.lean` opening explicitly leaves complete annotation/permission interpretation open. Research models R39/R41/R42 and R43 are conditional constructions, not semantic authority.

## Frozen inputs and output identity

Checkout source revisions supplied by the primary: pushed proposal head `b41e2433644ef7359af6ab68754804dbf1eb768d`, R42 source checkpoint `2182b07fbc7aa92c725634a78e0b2db3252e49e5`. No Git command ran in this leaf. Before construction, source baseline hashes matched contract: `candidate_effect.rs` = `82da9265af3bd663443550f4b113816cf2618c56e96014d9298c4563e875e6db`, `candidate_scheme.rs` = `c14f6cecb38fbf54b15e808f7385d9782dec1a784a12eac1315e1c32becd8429`. The concurrent Rust lane may change its leased source afterward; these are exact inspected baselines, not a claim about later bytes.

| Path | SHA-256 |
|---|---|
| `tasks/agent-loop/sprints/effect-permission-use-binding-20261031-r43.md` | `0e4e11482fe905f10229f08e015e3088f1da9bba3db04bd462241b9ecf920aed` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `questions/2026-10-16-annotation-declared-envelope/approved-answer.md` | `7c564a6e28c85059473b2c8498fdff72fd5f5e8f6378e9a8dce2780b63d69785` |
| `notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean` | `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e` |
| `notes/theory/lean/YulangClosure/LambdaArgumentEffectIncidenceR41.lean` | `af7c2e3def8762287e95827896dc01d982954059bff09c476d1a94df94c0a79e` |
| `notes/theory/lean/YulangClosure/NativeIncidenceAdapterR42.lean` | `61bb9ced2a80a75c2e952c3f5198a36ad7b9ae10f06df1a7996d38851107d4d6` |
| `notes/theory/lean/YulangClosure/UseScopedPermissionR43.lean` | `83ede0609353cec9dfde8258fa86f0f7c72aadef647dbe0819fe326776e46f8d` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `.agents/skills/yulang-lean-proofs/scripts/check_lean.py` | `a4f10b70297cbf4d8b5bc0c7526bc29783eaf417f1f70e53eeea341d1150dde6` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `crates/yu-solver/src/lib.rs` | `b1dac8bd244e282ff42a2d580e237393153f9b912c6ac0adf110367def5c79ce` |
| `crates/yu-solver/src/candidate_context.rs` | `030fcb4b6571c0db8a670d12d8a67fe8fcf465484502fe5b11b6d057e8026c38` |

Installed native executable: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`. Read-only version command `bwrap --ro-bind / / --dev /dev --proc /proc /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --version`, exit 0, printed `Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`. Project has no external Lake packages; pinned installed Std/Lean imports were trusted, without rebuilding or separately hashing their full compiled dependency closure. No Lake command, including version queries, ran.

## Source-to-model premises and exact limits

`candidate_effect.rs:434` owns `FormalEntryPermission`; `candidate_formal_entry_annotation` around 1833–1900 reads actual registration, owner-local Lambda/formal, source action/annotation/scope/row, and retains the ordered concrete vector. These fields correspond one-for-one to R39.Permission's registration, parameter recipe, formalIdentity, occurrence, owner, scope, annotationPosition, rowPosition, entry, concrete. `candidate_scheme.rs:436–497` baseline owns the R42 native certificate/partial extractor; it retains registration/Lambda, graph Function/child/row, native Function/child/mapped row, DefinitionUseId and context stamp.

For applying R43 to these exact source hashes, the Rust/source owner must independently establish:

1. `Id` is an equality-preserving representation of the COMPLETE branded source/effect identities, including effect type arguments and annotation scopes; keys are not spellings, row images or native Term images.
2. `permissions` is the complete ordered owning vector read from the actual state, without missing same-registration records or reconstructed/copied substitute payloads. The R43 selected singleton premise is exactly unique retention of the SAME R39 `p`; it is not established for Rust here.
3. `request a f r port` is extracted from the authentic current registration/action/annotation/row and owner-local Lambda. R41's full `Label` joins the actual registration/recipe/formal/owner/occurrence/scope/entry with its Lambda ordinal. In particular Rust's shorter R42 label must be joined through authentic source records, not fabricated into the rich label.
4. `reads` are the actual R42 retained route graph/term/row/native-store observations, and the supplied `use` is the exact route's DefinitionUseId AND FreshUse context. The three lookup/image equations in `constructed_entry_binding` must refer to that one capture/use mapping. Full R42 acceptance is a premise. No total maps or injectivity premise is added.

The theorem does not derive any of these source/native premises merely from a hash. Hashes identify the code being related. It also does not establish allocation, Rust lifetimes, error/rollback behavior, table completeness, actual lookup execution, provider arrival, permission consumption or a parent source judgment.

## Delivered declarations and parent application

All 11 delivered theorems are in namespace `YulangClosure.UseScopedPermissionR43`; complete `#check @` types and `#print axioms` outputs are retained below. `lookup_iff` characterizes singleton registration lookup; `accepted_iff` gives both directions of binding acceptance; `payload_preserved` retains the actual record and full certificate; `ordered_payload` gives equality of the whole retained record, concrete list and every list index, hence all duplicate positions/order. `absent_or_multiple_rejected` and `missing_or_ambiguous_rejected` cover unavailable/ambiguous lookup. `mismatch_rejected` covers owner, recipe/formal, occurrence, scope, annotation/row, entry, registration/full Lambda label, definition-use and context mismatch. `shared_images_distinct_bindings` retains distinct registrations despite shared Function/child/row images. Two fully instantiated numeric theorems witness success with `[7, 7, 11]` and the foreign/ambiguous rejection cases; they are finite mathematical examples, not runtime observations.

`constructed_entry_binding` applies `NativeIncidenceAdapterR42.constructed_entry_to_native` (which applies R41.entry_to_exact_use and R39 publication) and then `ComputationPermissionEntryR39.exact_row_retained` to that SAME `p`. It derives exact field matching and the R43 successful binding, retaining R39 preparation/publication, unchanged concrete payload, exact mapped Function/child/row and the actual positive native Function argument-effect field equation. It does not choose separate permission witnesses for publication and binding.

First remaining premise/owner: source/Rust lane and Luna must prove the exact extraction/completeness joins listed above, including `owningTable : ∀ p, permissionFor a f r port = some p → selected permissions a.registration = [p]`, at the reviewed R43 source hash. Next parent obstruction after binding remains authenticated actual inflow/arrival at a consumer, its source meaning and justified Catch/subtraction/residual behavior; owner Luna's source/consumer proof intake. The original parent remains OPEN even if those local R43 source joins pass review.

## Actual execution and audit route

Pinned elaboration command, cwd `notes/theory/lean`:

```sh
bwrap --ro-bind / / --dev /dev --proc /proc /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024
```

A parent Python `subprocess.run(input=source, text=True, capture_output=True, timeout=120)` constructs stdin in memory: initial `import Std`, `import Lean.Elab.Command`, `import Lean.Util.CollectAxioms`; complete R39, R41, R42 and R43 text in that order with only import lines removed; then the skill helper's `audit_source([], names)` with its redundant imports removed. The helper module was loaded by in-memory `exec(compile(...))` with an explicit `__file__`, never by its Lake main and without pycache. `audit_source` verifies theorem declaration kind and collects transitive axioms; `validate_audit` checks every ordered complete type/axiom receipt. The first invocation exposed actual diagnostics and was repaired; its failure output is retained below. The final invocation passed all 11 audits with no warnings or stderr.

Bounds: `LEAN_NUM_THREADS=1`, one CPU OS affinity inherited by bwrap/Lean via `os.sched_setaffinity`, process CPU RLIMIT_CPU 120s, `-j1`, `-M1024`, 120s subprocess wall timeout. No strict RLIMIT_AS address-space cap was attempted (R42 already documented toolchain thread creation failure under that cap); the retained pinned Lean memory cap is 1024MiB. Final observed child maximum RSS was 1,028,828 KiB, below 1GiB. Final CPU totals were not instrumented. Two Lean proof subprocesses took 9.188103s measured wall in aggregate; the read-only version probe also exited 0. Total dispatch-to-stop overhead was not independently instrumented; the full granted 1200s remains available for conservative accounting. No timeout or surviving process.

Axiom results: all theorems use `[propext]`, except `constructed_entry_binding`, which uses `[propext, Quot.sound]`; no `Classical.choice`, project axioms, `sorryAx` or native-evaluation assumptions. Source search of all four model files found only the word “admitted” in existing comments, no proof holes, project axioms or bypasses. Standard axioms and explicit theorem hypotheses are different evidence; audit acceptance establishes conditional Lean kernel acceptance only.


Pre-check Python helper import failed before Lean startup with `NameError: __file__ is not defined`; fixed by supplying the helper path in its module namespace. No Lean process or outputs from that attempt.

## Checker invocation 1

stdin SHA-256 `355f4502ce3ef1ce6c05fe581080aa9c1bbc9651d09f5785e47461aba3b181da`; exit 1; elapsed 6.774245s.

```text
<stdin>:964:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.UseScopedPermissionR43.lookup_iff`:
  [DecidableEq Id]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Id] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:999:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.UseScopedPermissionR43.accepted_iff`:
  [DecidableEq Term]
  [DecidableEq Row]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Term] [DecidableEq Row] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1047:41: error: typeclass instance problem is stuck
  GetElem? (List Id) ?m.31 (?m.50 i) (?m.53 i)

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `GetElem?` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
<stdin>:1053:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.UseScopedPermissionR43.missing_or_ambiguous_rejected`:
  [DecidableEq Term]
  [DecidableEq Row]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Term] [DecidableEq Row] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1062:0: warning: automatically included section variable(s) unused in theorem `YulangClosure.UseScopedPermissionR43.mismatch_rejected`:
  [DecidableEq Term]
  [DecidableEq Row]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [DecidableEq Term] [DecidableEq Row] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
<stdin>:1157:0: error: invalid 'import' command, it must be used in the beginning of the file
```

## Checker invocation 2

stdin SHA-256 `582224cf3fcbe0b57b2754565646cd1a8f6b436051efd6e249601ddea69c9e91`; exit 0; elapsed 2.413858s; stdout SHA-256 `e526d0df96670692d5d76978387efddbd44e9e8dd44fb95ea816fa698475969f`.

```text
YULANG_AUDIT_BEGIN YulangClosure.UseScopedPermissionR43.lookup_iff
@YulangClosure.UseScopedPermissionR43.lookup_iff : ∀ {Id : Type}
  (permissions : List (YulangClosure.ComputationPermissionEntryR39.Permission Id)) (registration : Nat)
  (p : YulangClosure.ComputationPermissionEntryR39.Permission Id),
  YulangClosure.UseScopedPermissionR43.lookup permissions registration = Option.some p ↔
    YulangClosure.UseScopedPermissionR43.selected permissions registration = [p]
'YulangClosure.UseScopedPermissionR43.lookup_iff' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.UseScopedPermissionR43.lookup_iff
YULANG_AUDIT_BEGIN YulangClosure.UseScopedPermissionR43.accepted_iff
@YulangClosure.UseScopedPermissionR43.accepted_iff : ∀ {Id Term Row DefinitionUse ContextUse : Type}
  [inst : DecidableEq Id] [inst_1 : DecidableEq DefinitionUse] [inst_2 : DecidableEq ContextUse]
  (permissions : List (YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (req : YulangClosure.UseScopedPermissionR43.Request Id)
  (use : YulangClosure.LambdaArgumentEffectIncidenceR41.Use DefinitionUse ContextUse)
  (c : YulangClosure.NativeIncidenceAdapterR42.Certificate Id Term Row DefinitionUse ContextUse)
  (out : YulangClosure.UseScopedPermissionR43.Binding Id Term Row DefinitionUse ContextUse),
  YulangClosure.UseScopedPermissionR43.bind permissions req use c = Option.some out ↔
    YulangClosure.UseScopedPermissionR43.selected permissions req.origin.registration = [out.permission] ∧
      YulangClosure.UseScopedPermissionR43.Matches req use out.permission c ∧ out.incidence = c
'YulangClosure.UseScopedPermissionR43.accepted_iff' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.UseScopedPermissionR43.accepted_iff
YULANG_AUDIT_BEGIN YulangClosure.UseScopedPermissionR43.payload_preserved
@YulangClosure.UseScopedPermissionR43.payload_preserved : ∀ {Id Term Row DefinitionUse ContextUse : Type}
  [inst : DecidableEq Id] [inst_1 : DecidableEq DefinitionUse] [inst_2 : DecidableEq ContextUse]
  (permissions : List (YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (req : YulangClosure.UseScopedPermissionR43.Request Id)
  (use : YulangClosure.LambdaArgumentEffectIncidenceR41.Use DefinitionUse ContextUse)
  (c : YulangClosure.NativeIncidenceAdapterR42.Certificate Id Term Row DefinitionUse ContextUse)
  (out : YulangClosure.UseScopedPermissionR43.Binding Id Term Row DefinitionUse ContextUse),
  YulangClosure.UseScopedPermissionR43.bind permissions req use c = Option.some out →
    YulangClosure.UseScopedPermissionR43.lookup permissions req.origin.registration = Option.some out.permission ∧
      out.incidence = c ∧ out.permission ∈ permissions
'YulangClosure.UseScopedPermissionR43.payload_preserved' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.UseScopedPermissionR43.payload_preserved
YULANG_AUDIT_BEGIN YulangClosure.UseScopedPermissionR43.ordered_payload
@YulangClosure.UseScopedPermissionR43.ordered_payload : ∀ {Id Term Row DefinitionUse ContextUse : Type}
  [inst : DecidableEq Id] [inst_1 : DecidableEq DefinitionUse] [inst_2 : DecidableEq ContextUse]
  (permissions : List (YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (req : YulangClosure.UseScopedPermissionR43.Request Id)
  (use : YulangClosure.LambdaArgumentEffectIncidenceR41.Use DefinitionUse ContextUse)
  (c : YulangClosure.NativeIncidenceAdapterR42.Certificate Id Term Row DefinitionUse ContextUse)
  (out : YulangClosure.UseScopedPermissionR43.Binding Id Term Row DefinitionUse ContextUse)
  (p : YulangClosure.ComputationPermissionEntryR39.Permission Id),
  YulangClosure.UseScopedPermissionR43.selected permissions req.origin.registration = [p] →
    YulangClosure.UseScopedPermissionR43.bind permissions req use c = Option.some out →
      out.permission = p ∧
        out.permission.concrete = p.concrete ∧ ∀ (i : Nat), out.permission.concrete[i]? = p.concrete[i]?
'YulangClosure.UseScopedPermissionR43.ordered_payload' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.UseScopedPermissionR43.ordered_payload
YULANG_AUDIT_BEGIN YulangClosure.UseScopedPermissionR43.missing_or_ambiguous_rejected
@YulangClosure.UseScopedPermissionR43.missing_or_ambiguous_rejected : ∀ {Id Term Row DefinitionUse ContextUse : Type}
  [inst : DecidableEq Id] [inst_1 : DecidableEq DefinitionUse] [inst_2 : DecidableEq ContextUse]
  (permissions : List (YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (req : YulangClosure.UseScopedPermissionR43.Request Id)
  (use : YulangClosure.LambdaArgumentEffectIncidenceR41.Use DefinitionUse ContextUse)
  (c : YulangClosure.NativeIncidenceAdapterR42.Certificate Id Term Row DefinitionUse ContextUse),
  YulangClosure.UseScopedPermissionR43.lookup permissions req.origin.registration = Option.none →
    YulangClosure.UseScopedPermissionR43.bind permissions req use c = Option.none
'YulangClosure.UseScopedPermissionR43.missing_or_ambiguous_rejected' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.UseScopedPermissionR43.missing_or_ambiguous_rejected
YULANG_AUDIT_BEGIN YulangClosure.UseScopedPermissionR43.absent_or_multiple_rejected
@YulangClosure.UseScopedPermissionR43.absent_or_multiple_rejected : ∀ {Id Term Row DefinitionUse ContextUse : Type}
  [inst : DecidableEq Id] [inst_1 : DecidableEq DefinitionUse] [inst_2 : DecidableEq ContextUse]
  (permissions : List (YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (req : YulangClosure.UseScopedPermissionR43.Request Id)
  (use : YulangClosure.LambdaArgumentEffectIncidenceR41.Use DefinitionUse ContextUse)
  (c : YulangClosure.NativeIncidenceAdapterR42.Certificate Id Term Row DefinitionUse ContextUse),
  (YulangClosure.UseScopedPermissionR43.selected permissions req.origin.registration = [] ∨
      ∃ p q tail, YulangClosure.UseScopedPermissionR43.selected permissions req.origin.registration = p :: q :: tail) →
    YulangClosure.UseScopedPermissionR43.bind permissions req use c = Option.none
'YulangClosure.UseScopedPermissionR43.absent_or_multiple_rejected' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.UseScopedPermissionR43.absent_or_multiple_rejected
YULANG_AUDIT_BEGIN YulangClosure.UseScopedPermissionR43.mismatch_rejected
@YulangClosure.UseScopedPermissionR43.mismatch_rejected : ∀ {Id Term Row DefinitionUse ContextUse : Type}
  [inst : DecidableEq Id] [inst_1 : DecidableEq DefinitionUse] [inst_2 : DecidableEq ContextUse]
  (permissions : List (YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (req : YulangClosure.UseScopedPermissionR43.Request Id)
  (use : YulangClosure.LambdaArgumentEffectIncidenceR41.Use DefinitionUse ContextUse)
  (c : YulangClosure.NativeIncidenceAdapterR42.Certificate Id Term Row DefinitionUse ContextUse)
  (p : YulangClosure.ComputationPermissionEntryR39.Permission Id),
  YulangClosure.UseScopedPermissionR43.selected permissions req.origin.registration = [p] →
    p.registration ≠ req.origin.registration ∨
        p.parameter ≠ req.origin.recipe ∨
          p.formalIdentity ≠ req.origin.formal ∨
            p.occurrence ≠ req.origin.occurrence ∨
              p.owner ≠ req.origin.owner ∨
                p.scope ≠ req.origin.scope ∨
                  p.annotationPosition ≠ req.annotationPosition ∨
                    p.rowPosition ≠ req.rowPosition ∨
                      p.entry ≠ req.origin.entry ∨
                        c.origin ≠ req.origin ∨
                          c.use.definitionUse ≠ use.definitionUse ∨ c.use.contextUse ≠ use.contextUse →
      YulangClosure.UseScopedPermissionR43.bind permissions req use c = Option.none
'YulangClosure.UseScopedPermissionR43.mismatch_rejected' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.UseScopedPermissionR43.mismatch_rejected
YULANG_AUDIT_BEGIN YulangClosure.UseScopedPermissionR43.shared_images_distinct_bindings
@YulangClosure.UseScopedPermissionR43.shared_images_distinct_bindings : ∀ {Id Term Row DefinitionUse ContextUse : Type}
  [inst : DecidableEq Id] [inst_1 : DecidableEq DefinitionUse] [inst_2 : DecidableEq ContextUse]
  (permissions : List (YulangClosure.ComputationPermissionEntryR39.Permission Id))
  (left right : YulangClosure.UseScopedPermissionR43.Request Id)
  (use : YulangClosure.LambdaArgumentEffectIncidenceR41.Use DefinitionUse ContextUse)
  (lc rc : YulangClosure.NativeIncidenceAdapterR42.Certificate Id Term Row DefinitionUse ContextUse)
  (lo ro : YulangClosure.UseScopedPermissionR43.Binding Id Term Row DefinitionUse ContextUse),
  YulangClosure.UseScopedPermissionR43.bind permissions left use lc = Option.some lo →
    YulangClosure.UseScopedPermissionR43.bind permissions right use rc = Option.some ro →
      left.origin.registration ≠ right.origin.registration →
        lc.function = rc.function →
          lc.child = rc.child →
            lc.mappedRow = rc.mappedRow →
              lo.incidence.function = ro.incidence.function ∧
                lo.incidence.child = ro.incidence.child ∧
                  lo.incidence.mappedRow = ro.incidence.mappedRow ∧
                    lo.permission.registration ≠ ro.permission.registration ∧ lo.permission ≠ ro.permission
'YulangClosure.UseScopedPermissionR43.shared_images_distinct_bindings' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.UseScopedPermissionR43.shared_images_distinct_bindings
YULANG_AUDIT_BEGIN YulangClosure.UseScopedPermissionR43.constructed_entry_binding
@YulangClosure.UseScopedPermissionR43.constructed_entry_binding : ∀ {Id Term Row DefinitionUse ContextUse : Type}
  [inst : DecidableEq Id] [inst_1 : DecidableEq DefinitionUse] [inst_2 : DecidableEq ContextUse]
  [inst_3 : DecidableEq Term] [inst_4 : DecidableEq Row] (e : YulangClosure.ComputationPermissionEntryR39.Inputs Id)
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id)
  (s : YulangClosure.ComputationPermissionEntryR39.State Id),
  e.formals[a.registration]? = Option.some f →
    a.annotation.row = Option.some r →
      f.entry = Option.some port →
        YulangClosure.ComputationPermissionEntryR39.Valid e a f r →
          r.concrete ≠ [] →
            ∀ (negativeEffect : Id → Term) (function argument returned result : Term) (nodes : Term → Nat)
              (rowIndexes : Id → Nat)
              (use : YulangClosure.LambdaArgumentEffectIncidenceR41.Use DefinitionUse ContextUse) (terms : Nat → Term)
              (rows : Nat → Row)
              (reads : YulangClosure.NativeIncidenceAdapterR42.Reads Term Row DefinitionUse ContextUse) (ordinal : Nat)
              (probe : YulangClosure.NativeIncidenceAdapterR42.Probe Term Row)
              (c : YulangClosure.NativeIncidenceAdapterR42.Certificate Id Term Row DefinitionUse ContextUse),
              YulangClosure.NativeIncidenceAdapterR42.extract
                    (YulangClosure.LambdaArgumentEffectIncidenceR41.capture nodes rowIndexes
                      (YulangClosure.LambdaArgumentEffectIncidenceR41.constructLambda a f port negativeEffect function
                        argument returned result))
                    use reads ordinal probe =
                  Option.some c →
                reads.terms (nodes function) = Option.some (terms (nodes function)) →
                  reads.terms (nodes (negativeEffect port)) = Option.some (terms (nodes (negativeEffect port))) →
                    reads.rows (rowIndexes port) = Option.some (rows (rowIndexes port)) →
                      ∀ (permissions : List (YulangClosure.ComputationPermissionEntryR39.Permission Id)),
                        (∀ (p : YulangClosure.ComputationPermissionEntryR39.Permission Id),
                            YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = Option.some p →
                              YulangClosure.UseScopedPermissionR43.selected permissions a.registration = [p]) →
                          ∃ p,
                            YulangClosure.ComputationPermissionEntryR39.prepare e a = Option.some (f, r, port) ∧
                              YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = Option.some p ∧
                                YulangClosure.ComputationPermissionEntryR39.publish a f r port Bool.true s =
                                    Option.some
                                      { permissions := s.permissions ++ [p],
                                        links :=
                                          s.links ++ YulangClosure.ComputationPermissionEntryR39.symbolicLinks a r port,
                                        inflow := s.inflow } ∧
                                  YulangClosure.UseScopedPermissionR43.bind permissions
                                        (YulangClosure.UseScopedPermissionR43.request a f r port) use c =
                                      Option.some { permission := p, incidence := c } ∧
                                    p.concrete = r.concrete ∧
                                      c.function = terms (nodes function) ∧
                                        c.child = terms (nodes (negativeEffect port)) ∧
                                          c.mappedRow = rows (rowIndexes port) ∧
                                            reads.nativeFunction c.function = Option.some probe.nativePorts ∧
                                              probe.nativePorts.argumentEffect = c.child
'YulangClosure.UseScopedPermissionR43.constructed_entry_binding' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.UseScopedPermissionR43.constructed_entry_binding
YULANG_AUDIT_BEGIN YulangClosure.UseScopedPermissionR43.shared_images_and_duplicate_order_witness
YulangClosure.UseScopedPermissionR43.shared_images_and_duplicate_order_witness : have ps :=
  [YulangClosure.UseScopedPermissionR43.witnessPermission 0, YulangClosure.UseScopedPermissionR43.witnessPermission 1];
YulangClosure.UseScopedPermissionR43.bind ps (YulangClosure.UseScopedPermissionR43.witnessRequest 0)
      { definitionUse := 100, contextUse := 200 } (YulangClosure.UseScopedPermissionR43.witnessCertificate 0) =
    Option.some
      { permission := YulangClosure.UseScopedPermissionR43.witnessPermission 0,
        incidence := YulangClosure.UseScopedPermissionR43.witnessCertificate 0 } ∧
  YulangClosure.UseScopedPermissionR43.bind ps (YulangClosure.UseScopedPermissionR43.witnessRequest 1)
        { definitionUse := 100, contextUse := 200 } (YulangClosure.UseScopedPermissionR43.witnessCertificate 1) =
      Option.some
        { permission := YulangClosure.UseScopedPermissionR43.witnessPermission 1,
          incidence := YulangClosure.UseScopedPermissionR43.witnessCertificate 1 } ∧
    (YulangClosure.UseScopedPermissionR43.witnessCertificate 0).function =
        (YulangClosure.UseScopedPermissionR43.witnessCertificate 1).function ∧
      (YulangClosure.UseScopedPermissionR43.witnessCertificate 0).child =
          (YulangClosure.UseScopedPermissionR43.witnessCertificate 1).child ∧
        (YulangClosure.UseScopedPermissionR43.witnessCertificate 0).mappedRow =
            (YulangClosure.UseScopedPermissionR43.witnessCertificate 1).mappedRow ∧
          YulangClosure.UseScopedPermissionR43.witnessPermission 0 ≠
              YulangClosure.UseScopedPermissionR43.witnessPermission 1 ∧
            (YulangClosure.UseScopedPermissionR43.witnessPermission 0).concrete = [7, 7, 11]
'YulangClosure.UseScopedPermissionR43.shared_images_and_duplicate_order_witness' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.UseScopedPermissionR43.shared_images_and_duplicate_order_witness
YULANG_AUDIT_BEGIN YulangClosure.UseScopedPermissionR43.foreign_and_ambiguous_witness
YulangClosure.UseScopedPermissionR43.foreign_and_ambiguous_witness : have ps :=
  [YulangClosure.UseScopedPermissionR43.witnessPermission 0];
YulangClosure.UseScopedPermissionR43.bind [] (YulangClosure.UseScopedPermissionR43.witnessRequest 0)
      { definitionUse := 100, contextUse := 200 } (YulangClosure.UseScopedPermissionR43.witnessCertificate 0) =
    Option.none ∧
  YulangClosure.UseScopedPermissionR43.bind
        [YulangClosure.UseScopedPermissionR43.witnessPermission 0,
          YulangClosure.UseScopedPermissionR43.witnessPermission 0]
        (YulangClosure.UseScopedPermissionR43.witnessRequest 0) { definitionUse := 100, contextUse := 200 }
        (YulangClosure.UseScopedPermissionR43.witnessCertificate 0) =
      Option.none ∧
    YulangClosure.UseScopedPermissionR43.bind ps (YulangClosure.UseScopedPermissionR43.witnessRequest 0)
          { definitionUse := 101, contextUse := 200 } (YulangClosure.UseScopedPermissionR43.witnessCertificate 0) =
        Option.none ∧
      YulangClosure.UseScopedPermissionR43.bind ps (YulangClosure.UseScopedPermissionR43.witnessRequest 0)
            { definitionUse := 100, contextUse := 201 } (YulangClosure.UseScopedPermissionR43.witnessCertificate 0) =
          Option.none ∧
        YulangClosure.UseScopedPermissionR43.bind ps (YulangClosure.UseScopedPermissionR43.witnessRequest 0)
              { definitionUse := 100, contextUse := 200 } (YulangClosure.UseScopedPermissionR43.witnessCertificate 1) =
            Option.none ∧
          YulangClosure.UseScopedPermissionR43.bind ps
                (have __src := YulangClosure.UseScopedPermissionR43.witnessRequest 0;
                { origin := __src.origin, annotationPosition := 81, rowPosition := __src.rowPosition })
                { definitionUse := 100, contextUse := 200 }
                (YulangClosure.UseScopedPermissionR43.witnessCertificate 0) =
              Option.none ∧
            YulangClosure.UseScopedPermissionR43.bind ps
                  (have __src := YulangClosure.UseScopedPermissionR43.witnessRequest 0;
                  { origin := __src.origin, annotationPosition := __src.annotationPosition, rowPosition := 91 })
                  { definitionUse := 100, contextUse := 200 }
                  (YulangClosure.UseScopedPermissionR43.witnessCertificate 0) =
                Option.none ∧
              YulangClosure.UseScopedPermissionR43.bind
                    [have __src := YulangClosure.UseScopedPermissionR43.witnessPermission 0;
                      { registration := __src.registration, parameter := __src.parameter,
                        formalIdentity := __src.formalIdentity, occurrence := __src.occurrence, owner := 12,
                        scope := __src.scope, annotationPosition := __src.annotationPosition,
                        rowPosition := __src.rowPosition, entry := __src.entry, concrete := __src.concrete }]
                    (YulangClosure.UseScopedPermissionR43.witnessRequest 0) { definitionUse := 100, contextUse := 200 }
                    (YulangClosure.UseScopedPermissionR43.witnessCertificate 0) =
                  Option.none ∧
                YulangClosure.UseScopedPermissionR43.bind
                      [have __src := YulangClosure.UseScopedPermissionR43.witnessPermission 0;
                        { registration := __src.registration, parameter := __src.parameter, formalIdentity := 32,
                          occurrence := __src.occurrence, owner := __src.owner, scope := __src.scope,
                          annotationPosition := __src.annotationPosition, rowPosition := __src.rowPosition,
                          entry := __src.entry, concrete := __src.concrete }]
                      (YulangClosure.UseScopedPermissionR43.witnessRequest 0)
                      { definitionUse := 100, contextUse := 200 }
                      (YulangClosure.UseScopedPermissionR43.witnessCertificate 0) =
                    Option.none ∧
                  YulangClosure.UseScopedPermissionR43.bind
                        [have __src := YulangClosure.UseScopedPermissionR43.witnessPermission 0;
                          { registration := __src.registration, parameter := __src.parameter,
                            formalIdentity := __src.formalIdentity, occurrence := __src.occurrence,
                            owner := __src.owner, scope := 62, annotationPosition := __src.annotationPosition,
                            rowPosition := __src.rowPosition, entry := __src.entry, concrete := __src.concrete }]
                        (YulangClosure.UseScopedPermissionR43.witnessRequest 0)
                        { definitionUse := 100, contextUse := 200 }
                        (YulangClosure.UseScopedPermissionR43.witnessCertificate 0) =
                      Option.none ∧
                    YulangClosure.UseScopedPermissionR43.bind ps (YulangClosure.UseScopedPermissionR43.witnessRequest 0)
                        { definitionUse := 100, contextUse := 200 }
                        (have __src := YulangClosure.UseScopedPermissionR43.witnessCertificate 0;
                        {
                          origin :=
                            have __src := (YulangClosure.UseScopedPermissionR43.witnessCertificate 0).origin;
                            { owner := __src.owner, registration := __src.registration, lambda := 21,
                              formal := __src.formal, recipe := __src.recipe, occurrence := __src.occurrence,
                              scope := __src.scope, entry := __src.entry },
                          use := __src.use, sourceFunction := __src.sourceFunction, sourceChild := __src.sourceChild,
                          sourceRow := __src.sourceRow, function := __src.function, child := __src.child,
                          mappedRow := __src.mappedRow }) =
                      Option.none
'YulangClosure.UseScopedPermissionR43.foreign_and_ambiguous_witness' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.UseScopedPermissionR43.foreign_and_ambiguous_witness
```

## STOP receipt

Frozen artifact: `notes/theory/lean/YulangClosure/UseScopedPermissionR43.lean`, SHA-256 `83ede0609353cec9dfde8258fa86f0f7c72aadef647dbe0819fe326776e46f8d`.
Sole handoff: `tasks/agent-loop/inbox/effect-permission-use-binding-r43-proof.md`.
Scratch/generated/import/cache/olean/target/worktree/environment paths: NONE. Exact writes: these two leased files only. No compiler/test/expectation/configuration/toolchain/manifest/status/index/question/Git changes. No children, scheduling, reviewer appointment, nested CLI or user/third-party contact. All subprocesses have exited. Writes STOPPED after this final handoff write; future changes require a new primary-directed packet. Independent review and source/production authority remain with the primary.

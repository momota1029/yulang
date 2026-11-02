# R286 caller-reference closure — producer handoff, revision 1

**Outcome:** conditional, kernel-checked local model results; general preservation **OPEN**. Producer `/root/sol_r286_caller_closure` (registered `lean_prover`, requested Sol/high; observed effective model/effort metadata unavailable), no descendants. Contract `tasks/agent-loop/sprints/extrusion-caller-closure-r286.md` SHA-256 `3d21c214ede8a82eceac2ddea3c9e85c6e41e48a1a6565ca45545bc5be1bd068`. Exact 33-input manifest SHA-256 `d61df1fdbb3ea46e34cc680a70bd4fdc8d6f26129680cc2b0423e86077efa814`; all 33 pins matched again after construction. R285 review receipt SHA-256 `2552ae69ff9defe2b8de7550223151fe4a60950810b614b8ea0b81cffb44b5f7`.

## Authority, model and premises

Original parent: `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1`, `notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md` §§1–3, 5, 7. Governing algorithm: Authoritative `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–3, including the §1.1 clarification. This module remains the `YulangClosure.OriginalExtrusionWork` model, not production source/native correspondence. No source domain, quantifier, shared-witness or semantics change is claimed. `R70`, Simple-sub A/B 0→0, source/native and production remain OPEN; `NO_SAFE_CODE_SLICE`.

`YulangClosure.OriginalExtrusionCallerClosureR286.ValueRefValid s endpoint` is exactly `ValueValid s endpoint ∧ ValueValid s (endpoint.rename s.qv)`. For `.row id`, those are `id < s.values.length ∧ s.qv id < s.values.length`. For a structural Value endpoint, the raw term label must satisfy `s.storedTerm term ≠ none`; rename leaves it unchanged. Rigid Value endpoints are valid by the model definition. `RequestValid s caller` checks **both** `caller.lower` and `caller.upper` this way. `SavedCallersValid s` quantifies every `parent ∈ s.parents` and checks both endpoints of `parent.operation.caller` against the **current** `s.values`, `s.terms`, and `s.qv`. `CallerClosure s := StorageClosed s ∧ CurrentCallerValid s ∧ SavedCallersValid s`. These definitions do not assume that production callers satisfy them.

`computed_rowInput_caller_closure_iff` proves exact initialization equivalence: `CallerClosure (Computed.rowInput caller) ↔ RequestValid (Computed.rowInput caller) caller`. The input's Value vector has length 2, terms are empty, and qv is identity. In particular arbitrary row IDs ≥2 and structural term labels without stored cells fail. `caller_closure_not_universal_computed_input` preserves R285's arbitrary-caller impossibility. The explicit `RequestValid` hypothesis is retained in the computed prefix and bound-request theorems.

## Checked application and remaining edge

The file proves raw/canonical caller frames under actual `State.allocate` (old qv representatives retained), `physicalInsert`, `internCell`, operation replacement/`initializeLocal`, `State.retain` Parent append, and both pre-link Parent publication failure and the post-append funding failure gate. It proves full `CallerClosure` through `select` queue removal, no-selected-work finish/failure, and selected Bound, IncomingAllowance, and EffectView, each with arbitrary `Funding` and either external or failed result. Selected memoized Visit, all three Aggregate slice failures, and the empty-children Function failure are checked subcases. The selected Bound theorem checks the emitted request against `resultState (step funds s)`, not only against the popped state. The computed three-step prefix has a separate direct `CallerClosure` proof under `RequestValid`; its bound request is valid against that prefix's returned state. `Computed.row_bound_produced` identifies that prefix result as external Bound. The direct prefix proof does **not** derive arbitrary-fuel preservation.

The unchanged proposed `step_preserves_caller_closure` was attempted without a hole. Its `select = none` goal closes via `no_selected_work_preserves_caller_closure`. The direct Lean diagnostic left exactly:

```text
funds : Funding
s : State
hs : CallerClosure s
task : Work
popped : State
hselect : select s = some (task, popped)
⊢ CallerClosure (resultState (perform funds popped task))
```

`caller_closure_select` now supplies `CallerClosure popped`, and three transfer-only constructors close. The first remaining model premise is full `perform` preservation for a new Visit (including row allocation, physical insertion, queue scheduling and structural discovery), nonempty Function rebuilding (including `internCell` publication before failure), and successful Tuple/Record/Variant processing (including memo publication and external output). All `.next`/`.external`/`.failed` projections and partial publication through those five mutation routes are **not** proved; no arbitrary-Funding `step_preserves_caller_closure` or arbitrary-fuel `runPrefix_preserves_caller_closure` declaration is delivered. An attempted broad unfolding of the computed prefix generated unresolved nested `visit`/`copiedRow` goals; the final direct computed proof instead uses the exact evaluated `rowBoundShape` and checks `StorageClosed` separately. An attempted exact `copiedRow` post-append-failure equation generated unresolved expanded state goals and was removed; `after_link_check_failure_caller_fields` is scoped to the actual gate after a successful `physicalInsert`. These failures are proof-state evidence, not counterexamples. There is no kernel-checked falsifier to universal preservation in this packet.

Applying the checked results to R70 still requires universal model `perform`/step/runPrefix preservation, then the separate production entry premise that every accepted constructor/session caller has the exact raw and canonical endpoint validity above. The source/session and `candidate_source`/`candidate_intrusion` initialization and mutation bridge owns that latter premise. The prior R70 W entry invariant, bound-fiber/source correspondence and later drain ownership also remain with their recorded owners. No conditional model theorem establishes production admission or source/native correspondence.

## Inputs, verification, resources and writes

Leased Lean artifact: `notes/theory/lean/YulangClosure/OriginalExtrusionCallerClosureR286.lean`, SHA-256 `06ee5e756eae0b863993af6aacef677701db91e00329cef7da44149195fb2e97`. Only this artifact, this handoff, and the exclusive `notes/theory/lean/.lake/build` cache were written. R283–R285, source, Rust, tests, toolchain/manifests, root imports, scheduling state and Git were untouched. No scratch path remains. Pinned `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake` reported Lake 5.0.0-src+eb6cafb / Lean 4.35.0; `lake env lean --version` reported Lean 4.35.0 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

Final focused `lake build +YulangClosure.OriginalExtrusionCallerClosureR286` exited 0 (16 jobs), direct `lake env lean -j1 -M1024 YulangClosure/OriginalExtrusionCallerClosureR286.lean` exited 0 with no diagnostics, and the bundled checker below exited 0 with **68/68** theorem type/axiom blocks and **68 PASS / 0 FAIL**. The source-cone `rg -n 'sorry|admit|^axiom|debug.skipKernelTC|unsafe|native_decide'` over this module and R283–R285/OriginalExtrusionWork returned exit 1, no matches. The complete printed types and per-theorem axiom lists follow; one `internCell_preserves_caller_store_fields` theorem has no axioms, while all other lists contain only permitted `propext`, `Quot.sound`, and where printed `Classical.choice`. This is kernel acceptance, not independent review or source correspondence. CPU/RSS were not measured; all focused commands completed without timeout within the 2,400-second assignment bound. **STOP / WRITES_STOPPED / NO DESCENDANTS.** Leases return to Luna for live reconciliation and fresh independent review; no carryover or Git action requested.

## Complete Lean theorem type and axiom audit

Checker command: `python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py --project /home/momota1029/rust/yulang/notes/theory/lean --lake /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --module YulangClosure.OriginalExtrusionCallerClosureR286 --timeout 240` plus the 68 exact `--theorem` names printed below.

```text
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --version
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
[exit 0]
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache env lean --version
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
[exit 0]
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache build +YulangClosure.OriginalExtrusionCallerClosureR286
Build completed successfully (16 jobs).
[exit 0]
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache env lean -j1 -M1024 --root=/tmp/yulang-lean-audit-galhc1l9 /tmp/yulang-lean-audit-galhc1l9/YulangProofAudit.lean
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_storage
YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_storage : ∀
  (s : YulangClosure.OriginalExtrusionWork.State),
  YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure s →
    YulangClosure.OriginalExtrusionStorageClosureR285.StorageClosed s
'YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_storage' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_storage
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_capture_complete
YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_capture_complete : ∀
  (s : YulangClosure.OriginalExtrusionWork.State),
  YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure s →
    YulangClosure.OriginalExtrusionCaptureValidityR284.CaptureComplete s
'YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_capture_complete' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_capture_complete
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.capture_gap_not_caller_closure
YulangClosure.OriginalExtrusionCallerClosureR286.capture_gap_not_caller_closure : ∀
  (caller : YulangClosure.NativeValueStructure.Request),
  ¬YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure
      (YulangClosure.OriginalExtrusionRowValidityR283.captureGap caller)
'YulangClosure.OriginalExtrusionCallerClosureR286.capture_gap_not_caller_closure' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.capture_gap_not_caller_closure
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.view_tail_gap_not_caller_closure
YulangClosure.OriginalExtrusionCallerClosureR286.view_tail_gap_not_caller_closure : ¬YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure
    YulangClosure.OriginalExtrusionCaptureValidityR284.viewTailGap
'YulangClosure.OriginalExtrusionCallerClosureR286.view_tail_gap_not_caller_closure' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.view_tail_gap_not_caller_closure
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_implies_r285
YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_implies_r285 : ∀
  (s : YulangClosure.OriginalExtrusionWork.State),
  YulangClosure.OriginalExtrusionCallerClosureR286.CurrentCallerValid s →
    YulangClosure.OriginalExtrusionStorageClosureR285.CallerRowsValid s
'YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_implies_r285' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_implies_r285
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_not_universal_computed_input
YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_not_universal_computed_input : ¬∀
    (caller : YulangClosure.NativeValueStructure.Request),
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure
      (YulangClosure.OriginalExtrusionWork.Computed.rowInput caller)
'YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_not_universal_computed_input' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_not_universal_computed_input
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.computed_rowInput_caller_closure_iff
YulangClosure.OriginalExtrusionCallerClosureR286.computed_rowInput_caller_closure_iff : ∀
  (caller : YulangClosure.NativeValueStructure.Request),
  YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure
      (YulangClosure.OriginalExtrusionWork.Computed.rowInput caller) ↔
    YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid
      (YulangClosure.OriginalExtrusionWork.Computed.rowInput caller) caller
'YulangClosure.OriginalExtrusionCallerClosureR286.computed_rowInput_caller_closure_iff' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.computed_rowInput_caller_closure_iff
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.computed_rowInput_caller_closure
YulangClosure.OriginalExtrusionCallerClosureR286.computed_rowInput_caller_closure : ∀
  (caller : YulangClosure.NativeValueStructure.Request),
  YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid
      (YulangClosure.OriginalExtrusionWork.Computed.rowInput caller) caller →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure
      (YulangClosure.OriginalExtrusionWork.Computed.rowInput caller)
'YulangClosure.OriginalExtrusionCallerClosureR286.computed_rowInput_caller_closure' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.computed_rowInput_caller_closure
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.value_valid_allocate
YulangClosure.OriginalExtrusionCallerClosureR286.value_valid_allocate : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (key : YulangClosure.OriginalExtrusionWork.CopyKey)
  (endpoint : YulangClosure.NativeValuePorts.ValueEndpoint),
  YulangClosure.OriginalExtrusionRowValidityR283.ValueValid s endpoint →
    YulangClosure.OriginalExtrusionRowValidityR283.ValueValid (s.allocate key) endpoint
'YulangClosure.OriginalExtrusionCallerClosureR286.value_valid_allocate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.value_valid_allocate
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.value_ref_valid_allocate
YulangClosure.OriginalExtrusionCallerClosureR286.value_ref_valid_allocate : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (key : YulangClosure.OriginalExtrusionWork.CopyKey)
  (endpoint : YulangClosure.NativeValuePorts.ValueEndpoint),
  YulangClosure.OriginalExtrusionCallerClosureR286.ValueRefValid s endpoint →
    YulangClosure.OriginalExtrusionCallerClosureR286.ValueRefValid (s.allocate key) endpoint
'YulangClosure.OriginalExtrusionCallerClosureR286.value_ref_valid_allocate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.value_ref_valid_allocate
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.request_valid_allocate
YulangClosure.OriginalExtrusionCallerClosureR286.request_valid_allocate : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (key : YulangClosure.OriginalExtrusionWork.CopyKey)
  (caller : YulangClosure.NativeValueStructure.Request),
  YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid s caller →
    YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid (s.allocate key) caller
'YulangClosure.OriginalExtrusionCallerClosureR286.request_valid_allocate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.request_valid_allocate
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.value_ref_valid_same_frame
YulangClosure.OriginalExtrusionCallerClosureR286.value_ref_valid_same_frame : ∀
  (s t : YulangClosure.OriginalExtrusionWork.State) (endpoint : YulangClosure.NativeValuePorts.ValueEndpoint),
  t.values.length = s.values.length →
    t.qv = s.qv →
      t.terms = s.terms →
        YulangClosure.OriginalExtrusionCallerClosureR286.ValueRefValid s endpoint →
          YulangClosure.OriginalExtrusionCallerClosureR286.ValueRefValid t endpoint
'YulangClosure.OriginalExtrusionCallerClosureR286.value_ref_valid_same_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.value_ref_valid_same_frame
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.request_valid_same_frame
YulangClosure.OriginalExtrusionCallerClosureR286.request_valid_same_frame : ∀
  (s t : YulangClosure.OriginalExtrusionWork.State) (caller : YulangClosure.NativeValueStructure.Request),
  t.values.length = s.values.length →
    t.qv = s.qv →
      t.terms = s.terms →
        YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid s caller →
          YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid t caller
'YulangClosure.OriginalExtrusionCallerClosureR286.request_valid_same_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.request_valid_same_frame
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.value_valid_mono
YulangClosure.OriginalExtrusionCallerClosureR286.value_valid_mono : ∀ (s t : YulangClosure.OriginalExtrusionWork.State)
  (endpoint : YulangClosure.NativeValuePorts.ValueEndpoint),
  s.values.length ≤ t.values.length →
    (∀ (term : Nat), s.storedTerm term ≠ Option.none → t.storedTerm term ≠ Option.none) →
      YulangClosure.OriginalExtrusionRowValidityR283.ValueValid s endpoint →
        YulangClosure.OriginalExtrusionRowValidityR283.ValueValid t endpoint
'YulangClosure.OriginalExtrusionCallerClosureR286.value_valid_mono' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.value_valid_mono
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.value_ref_valid_mono
YulangClosure.OriginalExtrusionCallerClosureR286.value_ref_valid_mono : ∀
  (s t : YulangClosure.OriginalExtrusionWork.State) (endpoint : YulangClosure.NativeValuePorts.ValueEndpoint),
  s.values.length ≤ t.values.length →
    (∀ (id : Nat), id < s.values.length → t.qv id = s.qv id) →
      (∀ (term : Nat), s.storedTerm term ≠ Option.none → t.storedTerm term ≠ Option.none) →
        YulangClosure.OriginalExtrusionCallerClosureR286.ValueRefValid s endpoint →
          YulangClosure.OriginalExtrusionCallerClosureR286.ValueRefValid t endpoint
'YulangClosure.OriginalExtrusionCallerClosureR286.value_ref_valid_mono' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.value_ref_valid_mono
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.request_valid_mono
YulangClosure.OriginalExtrusionCallerClosureR286.request_valid_mono : ∀
  (s t : YulangClosure.OriginalExtrusionWork.State) (caller : YulangClosure.NativeValueStructure.Request),
  s.values.length ≤ t.values.length →
    (∀ (id : Nat), id < s.values.length → t.qv id = s.qv id) →
      (∀ (term : Nat), s.storedTerm term ≠ Option.none → t.storedTerm term ≠ Option.none) →
        YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid s caller →
          YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid t caller
'YulangClosure.OriginalExtrusionCallerClosureR286.request_valid_mono' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.request_valid_mono
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_same_frame
YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_same_frame : ∀
  (s t : YulangClosure.OriginalExtrusionWork.State),
  t.operation = s.operation →
    t.values.length = s.values.length →
      t.qv = s.qv →
        t.terms = s.terms →
          t.parents = s.parents →
            YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid s →
              YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid t
'YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_same_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_same_frame
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_select
YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_select : ∀
  (s popped : YulangClosure.OriginalExtrusionWork.State) (task : YulangClosure.OriginalExtrusionWork.Work),
  YulangClosure.OriginalExtrusionWork.select s = Option.some (task, popped) →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid s →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid popped
'YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_select' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_select
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.rows_valid_work_tail
YulangClosure.OriginalExtrusionCallerClosureR286.rows_valid_work_tail : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (task : YulangClosure.OriginalExtrusionWork.Work)
  (rest : List YulangClosure.OriginalExtrusionWork.Work),
  YulangClosure.OriginalExtrusionRowValidityR283.RowsValid
      { operation := s.operation, qv := s.qv, qe := s.qe, values := s.values, effects := s.effects, terms := s.terms,
        termLabel := s.termLabel, termAllocations := s.termAllocations, views := s.views, captures := s.captures,
        rows := s.rows, structureMemo := s.structureMemo, work := task :: rest, pendingBounds := s.pendingBounds,
        tuplePorts := s.tuplePorts, parents := s.parents, pendingParents := s.pendingParents, calls := s.calls } →
    YulangClosure.OriginalExtrusionRowValidityR283.RowsValid
      { operation := s.operation, qv := s.qv, qe := s.qe, values := s.values, effects := s.effects, terms := s.terms,
        termLabel := s.termLabel, termAllocations := s.termAllocations, views := s.views, captures := s.captures,
        rows := s.rows, structureMemo := s.structureMemo, work := rest, pendingBounds := s.pendingBounds,
        tuplePorts := s.tuplePorts, parents := s.parents, pendingParents := s.pendingParents, calls := s.calls }
'YulangClosure.OriginalExtrusionCallerClosureR286.rows_valid_work_tail' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.rows_valid_work_tail
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.rows_valid_pending_tail
YulangClosure.OriginalExtrusionCallerClosureR286.rows_valid_pending_tail : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (task : YulangClosure.OriginalExtrusionWork.Work)
  (rest : List YulangClosure.OriginalExtrusionWork.Work),
  YulangClosure.OriginalExtrusionRowValidityR283.RowsValid
      { operation := s.operation, qv := s.qv, qe := s.qe, values := s.values, effects := s.effects, terms := s.terms,
        termLabel := s.termLabel, termAllocations := s.termAllocations, views := s.views, captures := s.captures,
        rows := s.rows, structureMemo := s.structureMemo, work := s.work, pendingBounds := task :: rest,
        tuplePorts := s.tuplePorts, parents := s.parents, pendingParents := s.pendingParents, calls := s.calls } →
    YulangClosure.OriginalExtrusionRowValidityR283.RowsValid
      { operation := s.operation, qv := s.qv, qe := s.qe, values := s.values, effects := s.effects, terms := s.terms,
        termLabel := s.termLabel, termAllocations := s.termAllocations, views := s.views, captures := s.captures,
        rows := s.rows, structureMemo := s.structureMemo, work := s.work, pendingBounds := rest,
        tuplePorts := s.tuplePorts, parents := s.parents, pendingParents := s.pendingParents, calls := s.calls }
'YulangClosure.OriginalExtrusionCallerClosureR286.rows_valid_pending_tail' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.rows_valid_pending_tail
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.view_refs_valid_work_tail
YulangClosure.OriginalExtrusionCallerClosureR286.view_refs_valid_work_tail : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (task : YulangClosure.OriginalExtrusionWork.Work)
  (rest : List YulangClosure.OriginalExtrusionWork.Work),
  YulangClosure.OriginalExtrusionStorageClosureR285.ViewRefsValid
      { operation := s.operation, qv := s.qv, qe := s.qe, values := s.values, effects := s.effects, terms := s.terms,
        termLabel := s.termLabel, termAllocations := s.termAllocations, views := s.views, captures := s.captures,
        rows := s.rows, structureMemo := s.structureMemo, work := task :: rest, pendingBounds := s.pendingBounds,
        tuplePorts := s.tuplePorts, parents := s.parents, pendingParents := s.pendingParents, calls := s.calls } →
    YulangClosure.OriginalExtrusionStorageClosureR285.ViewRefsValid
      { operation := s.operation, qv := s.qv, qe := s.qe, values := s.values, effects := s.effects, terms := s.terms,
        termLabel := s.termLabel, termAllocations := s.termAllocations, views := s.views, captures := s.captures,
        rows := s.rows, structureMemo := s.structureMemo, work := rest, pendingBounds := s.pendingBounds,
        tuplePorts := s.tuplePorts, parents := s.parents, pendingParents := s.pendingParents, calls := s.calls }
'YulangClosure.OriginalExtrusionCallerClosureR286.view_refs_valid_work_tail' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.view_refs_valid_work_tail
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.view_refs_valid_pending_tail
YulangClosure.OriginalExtrusionCallerClosureR286.view_refs_valid_pending_tail : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (task : YulangClosure.OriginalExtrusionWork.Work)
  (rest : List YulangClosure.OriginalExtrusionWork.Work),
  YulangClosure.OriginalExtrusionStorageClosureR285.ViewRefsValid
      { operation := s.operation, qv := s.qv, qe := s.qe, values := s.values, effects := s.effects, terms := s.terms,
        termLabel := s.termLabel, termAllocations := s.termAllocations, views := s.views, captures := s.captures,
        rows := s.rows, structureMemo := s.structureMemo, work := s.work, pendingBounds := task :: rest,
        tuplePorts := s.tuplePorts, parents := s.parents, pendingParents := s.pendingParents, calls := s.calls } →
    YulangClosure.OriginalExtrusionStorageClosureR285.ViewRefsValid
      { operation := s.operation, qv := s.qv, qe := s.qe, values := s.values, effects := s.effects, terms := s.terms,
        termLabel := s.termLabel, termAllocations := s.termAllocations, views := s.views, captures := s.captures,
        rows := s.rows, structureMemo := s.structureMemo, work := s.work, pendingBounds := rest,
        tuplePorts := s.tuplePorts, parents := s.parents, pendingParents := s.pendingParents, calls := s.calls }
'YulangClosure.OriginalExtrusionCallerClosureR286.view_refs_valid_pending_tail' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.view_refs_valid_pending_tail
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.storage_closed_work_tail
YulangClosure.OriginalExtrusionCallerClosureR286.storage_closed_work_tail : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (task : YulangClosure.OriginalExtrusionWork.Work)
  (rest : List YulangClosure.OriginalExtrusionWork.Work),
  YulangClosure.OriginalExtrusionStorageClosureR285.StorageClosed
      { operation := s.operation, qv := s.qv, qe := s.qe, values := s.values, effects := s.effects, terms := s.terms,
        termLabel := s.termLabel, termAllocations := s.termAllocations, views := s.views, captures := s.captures,
        rows := s.rows, structureMemo := s.structureMemo, work := task :: rest, pendingBounds := s.pendingBounds,
        tuplePorts := s.tuplePorts, parents := s.parents, pendingParents := s.pendingParents, calls := s.calls } →
    YulangClosure.OriginalExtrusionStorageClosureR285.StorageClosed
      { operation := s.operation, qv := s.qv, qe := s.qe, values := s.values, effects := s.effects, terms := s.terms,
        termLabel := s.termLabel, termAllocations := s.termAllocations, views := s.views, captures := s.captures,
        rows := s.rows, structureMemo := s.structureMemo, work := rest, pendingBounds := s.pendingBounds,
        tuplePorts := s.tuplePorts, parents := s.parents, pendingParents := s.pendingParents, calls := s.calls }
'YulangClosure.OriginalExtrusionCallerClosureR286.storage_closed_work_tail' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.storage_closed_work_tail
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.storage_closed_pending_tail
YulangClosure.OriginalExtrusionCallerClosureR286.storage_closed_pending_tail : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (task : YulangClosure.OriginalExtrusionWork.Work)
  (rest : List YulangClosure.OriginalExtrusionWork.Work),
  YulangClosure.OriginalExtrusionStorageClosureR285.StorageClosed
      { operation := s.operation, qv := s.qv, qe := s.qe, values := s.values, effects := s.effects, terms := s.terms,
        termLabel := s.termLabel, termAllocations := s.termAllocations, views := s.views, captures := s.captures,
        rows := s.rows, structureMemo := s.structureMemo, work := s.work, pendingBounds := task :: rest,
        tuplePorts := s.tuplePorts, parents := s.parents, pendingParents := s.pendingParents, calls := s.calls } →
    YulangClosure.OriginalExtrusionStorageClosureR285.StorageClosed
      { operation := s.operation, qv := s.qv, qe := s.qe, values := s.values, effects := s.effects, terms := s.terms,
        termLabel := s.termLabel, termAllocations := s.termAllocations, views := s.views, captures := s.captures,
        rows := s.rows, structureMemo := s.structureMemo, work := s.work, pendingBounds := rest,
        tuplePorts := s.tuplePorts, parents := s.parents, pendingParents := s.pendingParents, calls := s.calls }
'YulangClosure.OriginalExtrusionCallerClosureR286.storage_closed_pending_tail' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.storage_closed_pending_tail
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_select
YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_select : ∀
  (s popped : YulangClosure.OriginalExtrusionWork.State) (task : YulangClosure.OriginalExtrusionWork.Work),
  YulangClosure.OriginalExtrusionWork.select s = Option.some (task, popped) →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure s →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure popped
'YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_select' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_select
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_allocate
YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_allocate : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (key : YulangClosure.OriginalExtrusionWork.CopyKey),
  YulangClosure.OriginalExtrusionCallerClosureR286.CurrentCallerValid s →
    YulangClosure.OriginalExtrusionCallerClosureR286.CurrentCallerValid (s.allocate key)
'YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_allocate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_allocate
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_allocate
YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_allocate : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (key : YulangClosure.OriginalExtrusionWork.CopyKey),
  YulangClosure.OriginalExtrusionCallerClosureR286.SavedCallersValid s →
    YulangClosure.OriginalExtrusionCallerClosureR286.SavedCallersValid (s.allocate key)
'YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_allocate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_allocate
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_retain
YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_retain : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (key : YulangClosure.OriginalExtrusionWork.CopyKey)
  (copy : YulangClosure.OriginalExtrusionWork.Endpoint),
  YulangClosure.OriginalExtrusionCallerClosureR286.CurrentCallerValid s →
    YulangClosure.OriginalExtrusionCallerClosureR286.CurrentCallerValid (s.retain key copy)
'YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_retain' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_retain
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_retain
YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_retain : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (key : YulangClosure.OriginalExtrusionWork.CopyKey)
  (copy : YulangClosure.OriginalExtrusionWork.Endpoint),
  YulangClosure.OriginalExtrusionCallerClosureR286.SavedCallersValid s →
    YulangClosure.OriginalExtrusionCallerClosureR286.CurrentCallerValid s →
      YulangClosure.OriginalExtrusionCallerClosureR286.SavedCallersValid (s.retain key copy)
'YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_retain' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_retain
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_retain
YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_retain : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (key : YulangClosure.OriginalExtrusionWork.CopyKey)
  (copy : YulangClosure.OriginalExtrusionWork.Endpoint),
  YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid s →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid (s.retain key copy)
'YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_retain' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_retain
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_allocate
YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_allocate : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (key : YulangClosure.OriginalExtrusionWork.CopyKey),
  YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid s →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid (s.allocate key)
'YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_allocate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_allocate
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_physicalInsert
YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_physicalInsert : ∀
  (s t : YulangClosure.OriginalExtrusionWork.State) (raw : YulangClosure.OriginalExtrusionWork.RawBound),
  YulangClosure.OriginalExtrusionWork.physicalInsert s raw = Except.ok t →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid s →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid t
'YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_physicalInsert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_physicalInsert
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_prepared
YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_prepared : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (key : YulangClosure.OriginalExtrusionWork.CopyKey),
  YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid s →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid
      (YulangClosure.OriginalExtrusionWork.prepared s key)
'YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_prepared
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.failed_before_link_caller_fields
YulangClosure.OriginalExtrusionCallerClosureR286.failed_before_link_caller_fields : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (key : YulangClosure.OriginalExtrusionWork.CopyKey)
  (old : List YulangClosure.OriginalExtrusionWork.Endpoint) (error : YulangClosure.OriginalExtrusionWork.Failure),
  (match key.endpoint with
      | YulangClosure.OriginalExtrusionWork.Endpoint.value endpoint => s.values.length
      | YulangClosure.OriginalExtrusionWork.Endpoint.effect endpoint => s.effects.length) <
      2 ^ 32 →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid s →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid
        (YulangClosure.OriginalExtrusionRowValidityR283.resultState
          (YulangClosure.OriginalExtrusionWork.copiedRow
            (fun x point =>
              if point = YulangClosure.OriginalExtrusionWork.Check.linkBeforeAppend then Except.error error
              else Except.ok ())
            s key old))
'YulangClosure.OriginalExtrusionCallerClosureR286.failed_before_link_caller_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.failed_before_link_caller_fields
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_preLink
YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_preLink : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (key : YulangClosure.OriginalExtrusionWork.CopyKey),
  YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid s →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid
      (YulangClosure.OriginalExtrusionWork.preLink s key)
'YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_preLink' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_preLink
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_check_failure
YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_check_failure : ∀
  (funds : YulangClosure.OriginalExtrusionWork.Funding) (point : YulangClosure.OriginalExtrusionWork.Check)
  (s : YulangClosure.OriginalExtrusionWork.State)
  (next : YulangClosure.OriginalExtrusionWork.State → YulangClosure.OriginalExtrusionWork.Result)
  (error : YulangClosure.OriginalExtrusionWork.Failure),
  funds s.calls point = Except.error error →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid s →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid
        (YulangClosure.OriginalExtrusionRowValidityR283.resultState
          (YulangClosure.OriginalExtrusionWork.check funds point s next))
'YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_check_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_check_failure
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.internCell_preserves_caller_store_fields
YulangClosure.OriginalExtrusionCallerClosureR286.internCell_preserves_caller_store_fields : ∀
  (s t : YulangClosure.OriginalExtrusionWork.State) (cell : YulangClosure.OriginalExtrusionWork.StoredCell)
  (label : Nat),
  YulangClosure.OriginalExtrusionWork.internCell s cell = Except.ok (t, label) →
    t.operation = s.operation ∧ t.values = s.values ∧ t.qv = s.qv ∧ t.parents = s.parents
'YulangClosure.OriginalExtrusionCallerClosureR286.internCell_preserves_caller_store_fields' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.internCell_preserves_caller_store_fields
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_internCell
YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_internCell : ∀
  (s t : YulangClosure.OriginalExtrusionWork.State) (cell : YulangClosure.OriginalExtrusionWork.StoredCell)
  (label : Nat),
  YulangClosure.OriginalExtrusionWork.internCell s cell = Except.ok (t, label) →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid s →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid t
'YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_internCell' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_internCell
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.after_link_check_failure_caller_fields
YulangClosure.OriginalExtrusionCallerClosureR286.after_link_check_failure_caller_fields : ∀
  (funds : YulangClosure.OriginalExtrusionWork.Funding) (s linked : YulangClosure.OriginalExtrusionWork.State)
  (key : YulangClosure.OriginalExtrusionWork.CopyKey)
  (next : YulangClosure.OriginalExtrusionWork.State → YulangClosure.OriginalExtrusionWork.Result)
  (error : YulangClosure.OriginalExtrusionWork.Failure),
  YulangClosure.OriginalExtrusionWork.physicalInsert (YulangClosure.OriginalExtrusionWork.preLink s key)
        { owner := key.endpoint, polarity := YulangClosure.OriginalExtrusionWork.opposite key.polarity,
          endpoint := s.freshEndpoint key.endpoint } =
      Except.ok linked →
    funds linked.calls YulangClosure.OriginalExtrusionWork.Check.linkAfterAppend = Except.error error →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid s →
        YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid
          (YulangClosure.OriginalExtrusionRowValidityR283.resultState
            (YulangClosure.OriginalExtrusionWork.check funds YulangClosure.OriginalExtrusionWork.Check.linkAfterAppend
              linked next))
'YulangClosure.OriginalExtrusionCallerClosureR286.after_link_check_failure_caller_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.after_link_check_failure_caller_fields
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_replace
YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_replace : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (operation : YulangClosure.OriginalExtrusionWork.Operation),
  YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid s operation.caller →
    YulangClosure.OriginalExtrusionCallerClosureR286.CurrentCallerValid
      { operation := operation, qv := s.qv, qe := s.qe, values := s.values, effects := s.effects, terms := s.terms,
        termLabel := s.termLabel, termAllocations := s.termAllocations, views := s.views, captures := s.captures,
        rows := s.rows, structureMemo := s.structureMemo, work := s.work, pendingBounds := s.pendingBounds,
        tuplePorts := s.tuplePorts, parents := s.parents, pendingParents := s.pendingParents, calls := s.calls }
'YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_replace' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_replace
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_initializeLocal
YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_initializeLocal : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (operation : YulangClosure.OriginalExtrusionWork.Operation),
  YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid s operation.caller →
    YulangClosure.OriginalExtrusionCallerClosureR286.CurrentCallerValid
      (YulangClosure.OriginalExtrusionWork.initializeLocal s operation)
'YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_initializeLocal' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_initializeLocal
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_initializeLocal
YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_initializeLocal : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (operation : YulangClosure.OriginalExtrusionWork.Operation),
  YulangClosure.OriginalExtrusionCallerClosureR286.SavedCallersValid s →
    YulangClosure.OriginalExtrusionCallerClosureR286.SavedCallersValid
      (YulangClosure.OriginalExtrusionWork.initializeLocal s operation)
'YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_initializeLocal' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_initializeLocal
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_replace
YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_replace : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (operation : YulangClosure.OriginalExtrusionWork.Operation),
  YulangClosure.OriginalExtrusionCallerClosureR286.SavedCallersValid s →
    YulangClosure.OriginalExtrusionCallerClosureR286.SavedCallersValid
      { operation := operation, qv := s.qv, qe := s.qe, values := s.values, effects := s.effects, terms := s.terms,
        termLabel := s.termLabel, termAllocations := s.termAllocations, views := s.views, captures := s.captures,
        rows := s.rows, structureMemo := s.structureMemo, work := s.work, pendingBounds := s.pendingBounds,
        tuplePorts := s.tuplePorts, parents := s.parents, pendingParents := s.pendingParents, calls := s.calls }
'YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_replace' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_replace
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_initializeLocal
YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_initializeLocal : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (operation : YulangClosure.OriginalExtrusionWork.Operation),
  YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid s operation.caller →
    YulangClosure.OriginalExtrusionCallerClosureR286.SavedCallersValid s →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid
        (YulangClosure.OriginalExtrusionWork.initializeLocal s operation)
'YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_initializeLocal' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_initializeLocal
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.bound_request_caller_valid
YulangClosure.OriginalExtrusionCallerClosureR286.bound_request_caller_valid : ∀
  (s : YulangClosure.OriginalExtrusionWork.State) (owner : YulangClosure.OriginalExtrusionWork.Endpoint)
  (p : YulangClosure.NativeMergeExpansion.Polarity) (copied : YulangClosure.OriginalExtrusionWork.Endpoint)
  (source : YulangClosure.OriginalExtrusionWork.RawBound),
  YulangClosure.OriginalExtrusionCallerClosureR286.CurrentCallerValid s →
    YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid s
      (YulangClosure.OriginalExtrusionWork.boundRequest s owner p copied source).operation.caller
'YulangClosure.OriginalExtrusionCallerClosureR286.bound_request_caller_valid' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.bound_request_caller_valid
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_external_caller_valid
YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_external_caller_valid : ∀
  (funds : YulangClosure.OriginalExtrusionWork.Funding) (s popped : YulangClosure.OriginalExtrusionWork.State)
  (owner : YulangClosure.OriginalExtrusionWork.Endpoint) (p : YulangClosure.NativeMergeExpansion.Polarity)
  (child : YulangClosure.OriginalExtrusionWork.CopyKey) (source : YulangClosure.OriginalExtrusionWork.RawBound)
  (copied : YulangClosure.OriginalExtrusionWork.Endpoint),
  YulangClosure.OriginalExtrusionWork.select s =
      Option.some (YulangClosure.OriginalExtrusionWork.Work.bound owner p child source, popped) →
    popped.lookup child = Option.some copied →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid s →
        YulangClosure.OriginalExtrusionWork.step funds s =
            YulangClosure.OriginalExtrusionWork.Result.external popped
              (YulangClosure.OriginalExtrusionWork.External.bound
                (YulangClosure.OriginalExtrusionWork.boundRequest popped owner p copied source)) ∧
          YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid popped
            (YulangClosure.OriginalExtrusionWork.boundRequest popped owner p copied source).operation.caller
'YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_external_caller_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_external_caller_valid
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_external_result_caller_valid
YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_external_result_caller_valid : ∀
  (funds : YulangClosure.OriginalExtrusionWork.Funding) (s popped : YulangClosure.OriginalExtrusionWork.State)
  (owner : YulangClosure.OriginalExtrusionWork.Endpoint) (p : YulangClosure.NativeMergeExpansion.Polarity)
  (child : YulangClosure.OriginalExtrusionWork.CopyKey) (source : YulangClosure.OriginalExtrusionWork.RawBound)
  (copied : YulangClosure.OriginalExtrusionWork.Endpoint),
  YulangClosure.OriginalExtrusionWork.select s =
      Option.some (YulangClosure.OriginalExtrusionWork.Work.bound owner p child source, popped) →
    popped.lookup child = Option.some copied →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure s →
        YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid
          (YulangClosure.OriginalExtrusionRowValidityR283.resultState
            (YulangClosure.OriginalExtrusionWork.step funds s))
          (YulangClosure.OriginalExtrusionWork.boundRequest popped owner p copied source).operation.caller
'YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_external_result_caller_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_external_result_caller_valid
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_caller_fields
YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_caller_fields : ∀
  (funds : YulangClosure.OriginalExtrusionWork.Funding) (s popped : YulangClosure.OriginalExtrusionWork.State)
  (owner : YulangClosure.OriginalExtrusionWork.Endpoint) (p : YulangClosure.NativeMergeExpansion.Polarity)
  (child : YulangClosure.OriginalExtrusionWork.CopyKey) (source : YulangClosure.OriginalExtrusionWork.RawBound),
  YulangClosure.OriginalExtrusionWork.select s =
      Option.some (YulangClosure.OriginalExtrusionWork.Work.bound owner p child source, popped) →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid s →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid
        (YulangClosure.OriginalExtrusionRowValidityR283.resultState (YulangClosure.OriginalExtrusionWork.step funds s))
'YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_caller_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_caller_fields
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.selected_incoming_caller_fields
YulangClosure.OriginalExtrusionCallerClosureR286.selected_incoming_caller_fields : ∀
  (funds : YulangClosure.OriginalExtrusionWork.Funding) (s popped : YulangClosure.OriginalExtrusionWork.State)
  (tail view : Nat) (source : YulangClosure.OriginalExtrusionWork.CopyKey)
  (original : YulangClosure.OriginalExtrusionWork.RawBound),
  YulangClosure.OriginalExtrusionWork.select s =
      Option.some (YulangClosure.OriginalExtrusionWork.Work.incomingAllowance tail view source original, popped) →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid s →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid
        (YulangClosure.OriginalExtrusionRowValidityR283.resultState (YulangClosure.OriginalExtrusionWork.step funds s))
'YulangClosure.OriginalExtrusionCallerClosureR286.selected_incoming_caller_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.selected_incoming_caller_fields
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.selected_effect_view_caller_fields
YulangClosure.OriginalExtrusionCallerClosureR286.selected_effect_view_caller_fields : ∀
  (funds : YulangClosure.OriginalExtrusionWork.Funding) (s popped : YulangClosure.OriginalExtrusionWork.State)
  (key : YulangClosure.OriginalExtrusionWork.CopyKey) (view : Nat)
  (child : YulangClosure.OriginalExtrusionWork.CopyKey),
  YulangClosure.OriginalExtrusionWork.select s =
      Option.some (YulangClosure.OriginalExtrusionWork.Work.effectView key view child, popped) →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid s →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid
        (YulangClosure.OriginalExtrusionRowValidityR283.resultState (YulangClosure.OriginalExtrusionWork.step funds s))
'YulangClosure.OriginalExtrusionCallerClosureR286.selected_effect_view_caller_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.selected_effect_view_caller_fields
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_preserves_caller_closure
YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_preserves_caller_closure : ∀
  (funds : YulangClosure.OriginalExtrusionWork.Funding) (s popped : YulangClosure.OriginalExtrusionWork.State)
  (owner : YulangClosure.OriginalExtrusionWork.Endpoint) (p : YulangClosure.NativeMergeExpansion.Polarity)
  (child : YulangClosure.OriginalExtrusionWork.CopyKey) (source : YulangClosure.OriginalExtrusionWork.RawBound),
  YulangClosure.OriginalExtrusionWork.select s =
      Option.some (YulangClosure.OriginalExtrusionWork.Work.bound owner p child source, popped) →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure s →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure
        (YulangClosure.OriginalExtrusionRowValidityR283.resultState (YulangClosure.OriginalExtrusionWork.step funds s))
'YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_preserves_caller_closure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_preserves_caller_closure
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.selected_memoized_visit_preserves_caller_closure
YulangClosure.OriginalExtrusionCallerClosureR286.selected_memoized_visit_preserves_caller_closure : ∀
  (funds : YulangClosure.OriginalExtrusionWork.Funding) (s popped : YulangClosure.OriginalExtrusionWork.State)
  (key : YulangClosure.OriginalExtrusionWork.CopyKey) (copied : YulangClosure.OriginalExtrusionWork.Endpoint),
  YulangClosure.OriginalExtrusionWork.select s =
      Option.some (YulangClosure.OriginalExtrusionWork.Work.visit key, popped) →
    popped.rows key = Option.some copied →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure s →
        YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure
          (YulangClosure.OriginalExtrusionRowValidityR283.resultState
            (YulangClosure.OriginalExtrusionWork.step funds s))
'YulangClosure.OriginalExtrusionCallerClosureR286.selected_memoized_visit_preserves_caller_closure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.selected_memoized_visit_preserves_caller_closure
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.selected_aggregate_slice_failure_preserves_caller_closure
YulangClosure.OriginalExtrusionCallerClosureR286.selected_aggregate_slice_failure_preserves_caller_closure : ∀
  (funds : YulangClosure.OriginalExtrusionWork.Funding) (s popped : YulangClosure.OriginalExtrusionWork.State)
  (kind : YulangClosure.OriginalExtrusionWork.Aggregate) (key : YulangClosure.OriginalExtrusionWork.CopyKey)
  (start len : Nat) (error : YulangClosure.OriginalExtrusionWork.Failure),
  YulangClosure.OriginalExtrusionWork.select s =
      Option.some (YulangClosure.OriginalExtrusionWork.aggregateWork kind key start len, popped) →
    YulangClosure.OriginalExtrusionWork.slice popped start len
          (if kind = YulangClosure.OriginalExtrusionWork.Aggregate.tuple then
            YulangClosure.OriginalExtrusionWork.Failure.identityExhausted
          else YulangClosure.OriginalExtrusionWork.Failure.receiptMismatch) =
        Except.error error →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure s →
        YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure
          (YulangClosure.OriginalExtrusionRowValidityR283.resultState
            (YulangClosure.OriginalExtrusionWork.step funds s))
'YulangClosure.OriginalExtrusionCallerClosureR286.selected_aggregate_slice_failure_preserves_caller_closure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.selected_aggregate_slice_failure_preserves_caller_closure
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.selected_empty_function_failure_preserves_caller_closure
YulangClosure.OriginalExtrusionCallerClosureR286.selected_empty_function_failure_preserves_caller_closure : ∀
  (funds : YulangClosure.OriginalExtrusionWork.Funding) (s popped : YulangClosure.OriginalExtrusionWork.State)
  (key : YulangClosure.OriginalExtrusionWork.CopyKey) (originals : YulangClosure.NativeValuePorts.FunctionTerms),
  YulangClosure.OriginalExtrusionWork.select s =
      Option.some (YulangClosure.OriginalExtrusionWork.Work.function key [] originals, popped) →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure s →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure
        (YulangClosure.OriginalExtrusionRowValidityR283.resultState (YulangClosure.OriginalExtrusionWork.step funds s))
'YulangClosure.OriginalExtrusionCallerClosureR286.selected_empty_function_failure_preserves_caller_closure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.selected_empty_function_failure_preserves_caller_closure
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.selected_incoming_preserves_caller_closure
YulangClosure.OriginalExtrusionCallerClosureR286.selected_incoming_preserves_caller_closure : ∀
  (funds : YulangClosure.OriginalExtrusionWork.Funding) (s popped : YulangClosure.OriginalExtrusionWork.State)
  (tail view : Nat) (source : YulangClosure.OriginalExtrusionWork.CopyKey)
  (original : YulangClosure.OriginalExtrusionWork.RawBound),
  YulangClosure.OriginalExtrusionWork.select s =
      Option.some (YulangClosure.OriginalExtrusionWork.Work.incomingAllowance tail view source original, popped) →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure s →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure
        (YulangClosure.OriginalExtrusionRowValidityR283.resultState (YulangClosure.OriginalExtrusionWork.step funds s))
'YulangClosure.OriginalExtrusionCallerClosureR286.selected_incoming_preserves_caller_closure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.selected_incoming_preserves_caller_closure
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.selected_effect_view_preserves_caller_closure
YulangClosure.OriginalExtrusionCallerClosureR286.selected_effect_view_preserves_caller_closure : ∀
  (funds : YulangClosure.OriginalExtrusionWork.Funding) (s popped : YulangClosure.OriginalExtrusionWork.State)
  (key : YulangClosure.OriginalExtrusionWork.CopyKey) (view : Nat)
  (child : YulangClosure.OriginalExtrusionWork.CopyKey),
  YulangClosure.OriginalExtrusionWork.select s =
      Option.some (YulangClosure.OriginalExtrusionWork.Work.effectView key view child, popped) →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure s →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure
        (YulangClosure.OriginalExtrusionRowValidityR283.resultState (YulangClosure.OriginalExtrusionWork.step funds s))
'YulangClosure.OriginalExtrusionCallerClosureR286.selected_effect_view_preserves_caller_closure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.selected_effect_view_preserves_caller_closure
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.no_selected_work_preserves_caller_closure
YulangClosure.OriginalExtrusionCallerClosureR286.no_selected_work_preserves_caller_closure : ∀
  (funds : YulangClosure.OriginalExtrusionWork.Funding) (s : YulangClosure.OriginalExtrusionWork.State),
  YulangClosure.OriginalExtrusionWork.select s = Option.none →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure s →
      YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure
        (YulangClosure.OriginalExtrusionRowValidityR283.resultState (YulangClosure.OriginalExtrusionWork.step funds s))
'YulangClosure.OriginalExtrusionCallerClosureR286.no_selected_work_preserves_caller_closure' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.no_selected_work_preserves_caller_closure
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_caller_eq
YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_caller_eq : ∀
  (caller : YulangClosure.NativeValueStructure.Request),
  (YulangClosure.OriginalExtrusionWork.Computed.rowBoundState caller).operation.caller = caller
'YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_caller_eq' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_caller_eq
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_values_length
YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_values_length : ∀
  (caller : YulangClosure.NativeValueStructure.Request),
  (YulangClosure.OriginalExtrusionWork.Computed.rowBoundState caller).values.length = 3
'YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_values_length' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_values_length
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_terms
YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_terms : ∀
  (caller : YulangClosure.NativeValueStructure.Request),
  (YulangClosure.OriginalExtrusionWork.Computed.rowBoundState caller).terms = []
'YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_terms' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_terms
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_qv
YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_qv : ∀
  (caller : YulangClosure.NativeValueStructure.Request) (id : Nat),
  (YulangClosure.OriginalExtrusionWork.Computed.rowBoundState caller).qv id = id
'YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_qv' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_qv
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_parents
YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_parents : ∀
  (caller : YulangClosure.NativeValueStructure.Request),
  (YulangClosure.OriginalExtrusionWork.Computed.rowBoundState caller).parents =
    [{ copy := YulangClosure.OriginalExtrusionWork.Endpoint.value (YulangClosure.NativeValuePorts.ValueEndpoint.row 2),
        parent :=
          YulangClosure.OriginalExtrusionWork.Endpoint.value (YulangClosure.NativeValuePorts.ValueEndpoint.row 0),
        polarity := YulangClosure.NativeMergeExpansion.Polarity.negative, target := 1,
        operation := (YulangClosure.OriginalExtrusionWork.Computed.rowInput caller).operation }]
'YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_parents' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_parents
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_caller_fields
YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_caller_fields : ∀
  (caller : YulangClosure.NativeValueStructure.Request),
  YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid
      (YulangClosure.OriginalExtrusionWork.Computed.rowInput caller) caller →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerFieldsValid
      (YulangClosure.OriginalExtrusionWork.Computed.rowBoundState caller)
'YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_caller_fields' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_caller_fields
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.computed_bound_request_caller_valid
YulangClosure.OriginalExtrusionCallerClosureR286.computed_bound_request_caller_valid : ∀
  (caller : YulangClosure.NativeValueStructure.Request),
  YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid
      (YulangClosure.OriginalExtrusionWork.Computed.rowInput caller) caller →
    YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid
      (YulangClosure.OriginalExtrusionWork.Computed.rowBoundState caller)
      (YulangClosure.OriginalExtrusionWork.Computed.rowBoundRequest caller).operation.caller
'YulangClosure.OriginalExtrusionCallerClosureR286.computed_bound_request_caller_valid' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.computed_bound_request_caller_valid
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.computed_prefix_bound_result_caller_valid
YulangClosure.OriginalExtrusionCallerClosureR286.computed_prefix_bound_result_caller_valid : ∀
  (caller : YulangClosure.NativeValueStructure.Request),
  YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid
      (YulangClosure.OriginalExtrusionWork.Computed.rowInput caller) caller →
    YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid
      (YulangClosure.OriginalExtrusionRowValidityR283.resultState
        (YulangClosure.OriginalExtrusionWork.runPrefix YulangClosure.OriginalExtrusionWork.funded 3
          (YulangClosure.OriginalExtrusionWork.Computed.rowInput caller)))
      (YulangClosure.OriginalExtrusionWork.Computed.rowBoundRequest caller).operation.caller
'YulangClosure.OriginalExtrusionCallerClosureR286.computed_prefix_bound_result_caller_valid' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.computed_prefix_bound_result_caller_valid
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.rowBoundShape_eq
YulangClosure.OriginalExtrusionCallerClosureR286.rowBoundShape_eq : ∀
  (caller : YulangClosure.NativeValueStructure.Request),
  YulangClosure.OriginalExtrusionWork.Computed.rowBoundState caller =
    YulangClosure.OriginalExtrusionCallerClosureR286.rowBoundShape caller
'YulangClosure.OriginalExtrusionCallerClosureR286.rowBoundShape_eq' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.rowBoundShape_eq
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_storage
YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_storage : ∀
  (caller : YulangClosure.NativeValueStructure.Request),
  YulangClosure.OriginalExtrusionStorageClosureR285.StorageClosed
    (YulangClosure.OriginalExtrusionWork.Computed.rowBoundState caller)
'YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_storage' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_storage
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_prefix_caller_closure
YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_prefix_caller_closure : ∀
  (caller : YulangClosure.NativeValueStructure.Request),
  YulangClosure.OriginalExtrusionCallerClosureR286.RequestValid
      (YulangClosure.OriginalExtrusionWork.Computed.rowInput caller) caller →
    YulangClosure.OriginalExtrusionCallerClosureR286.CallerClosure
      (YulangClosure.OriginalExtrusionRowValidityR283.resultState
        (YulangClosure.OriginalExtrusionWork.runPrefix YulangClosure.OriginalExtrusionWork.funded 3
          (YulangClosure.OriginalExtrusionWork.Computed.rowInput caller)))
'YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_prefix_caller_closure' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_prefix_caller_closure
[exit 0]
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_storage, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_capture_complete, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.capture_gap_not_caller_closure, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.view_tail_gap_not_caller_closure, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_implies_r285, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_not_universal_computed_input, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.computed_rowInput_caller_closure_iff, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.computed_rowInput_caller_closure, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.value_valid_allocate, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.value_ref_valid_allocate, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.request_valid_allocate, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.value_ref_valid_same_frame, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.request_valid_same_frame, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.value_valid_mono, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.value_ref_valid_mono, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.request_valid_mono, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_same_frame, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_select, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.rows_valid_work_tail, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.rows_valid_pending_tail, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.view_refs_valid_work_tail, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.view_refs_valid_pending_tail, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.storage_closed_work_tail, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.storage_closed_pending_tail, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.caller_closure_select, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_allocate, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_allocate, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_retain, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_retain, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_retain, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_allocate, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_physicalInsert, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_prepared, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.failed_before_link_caller_fields, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_preLink, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_check_failure, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.internCell_preserves_caller_store_fields, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_internCell, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.after_link_check_failure_caller_fields, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_replace, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.current_caller_valid_initializeLocal, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_initializeLocal, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.saved_callers_valid_replace, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.caller_fields_valid_initializeLocal, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.bound_request_caller_valid, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_external_caller_valid, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_external_result_caller_valid, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_caller_fields, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.selected_incoming_caller_fields, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.selected_effect_view_caller_fields, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.selected_bound_preserves_caller_closure, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.selected_memoized_visit_preserves_caller_closure, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.selected_aggregate_slice_failure_preserves_caller_closure, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.selected_empty_function_failure_preserves_caller_closure, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.selected_incoming_preserves_caller_closure, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.selected_effect_view_preserves_caller_closure, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.no_selected_work_preserves_caller_closure, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_caller_eq, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_values_length, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_terms, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_qv, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_parents, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_caller_fields, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.computed_bound_request_caller_valid, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.computed_prefix_bound_result_caller_valid, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.rowBoundShape_eq, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_bound_storage, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionCallerClosureR286.computed_row_prefix_caller_closure, under its printed hypotheses; axiom whitelist satisfied.
Named declarations only; ordinary-mistake check, not independent review or source correspondence.

[checker exit 0]
```

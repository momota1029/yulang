# R283 Sol proof handoff — draft until STOP

## Gate and scope

- Contract SHA-256 `6ef81be17b0a3377e2563967ba515c7f31bba6dfec9ccc7f164b46d22c5a4885`; admission SHA-256 `08d12924daa02dc577ad91ad8ee9a55df909193f33aea48a4afa1dbaee70e887`.
- All 11 imported module hashes and all three config hashes match the admission table before construction. The imported `OriginalExtrusionWork.lean` is `c419675d75a2cdf03fe5b1ba8d2eef106fea0c4f5187f9f5c06999fa734edd58`.
- Native Lake `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`: `5.0.0-src+eb6cafb` (Lean 4.35.0), exit 0. `lake env lean --version`: Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, exit 0.
- Source authority: `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §1 and §1.1 (Authoritative ordinary level based extrusion); `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §1 (original full source, history, occurrence, scope and shared witness claim remains OPEN); `docs/yulang-whole-proof-closure-ja.md` §1 and §4.2 (inference soundness and remaining extrusion bridge). The local mathematical object is the already pinned `YulangClosure.OriginalExtrusionWork` model, especially `State`, `Result`, `Work`, `incomingJobs`, `copiedRow`, `step`, `runPrefix` and `Computed.rowInput`; these are not original source semantics.
- Parent edge: `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1`. Original full source inference soundness, Simple-sub A/B, source/native correspondence and R70 W remain open. Parent/A/B `0->0`; `NO_SAFE_CODE_SLICE`. This trial cannot close any source or Rust premise.

## Constructed counterexample

`YulangClosure.OriginalExtrusionRowValidityR283.RowsValid` is a non-tautological candidate requiring valid operation root, in-range canonical row representatives, both stored row vectors and atoms, every stored cell row and child term, both memo functions' keys and images, all eight Work constructors in both queues, tuple ports, Parents and pending Parent indices. It intentionally omits `State.captures` incidence sources. `resultState` projects all three actual Result constructors.

`captureGap gapCaller` has one valid effect row at level 2, positive Visit with target 1, and a capture incidence at row 0 whose source is row 99. Its candidate invariant holds. The actual `step funded` takes the high-row copy path, allocates effect row 1, retains and links the parent, then `incomingJobs` puts `.visit ⟨.effect (.row 99), .positive, 1⟩` in `pendingBounds`. The post-state has only two effect rows. Therefore `RowsValid` fails. Fuel-1 `runPrefix funded` returns the same invalid state. This is an actual model counterexample to the proposed candidate invariant, not a source-language counterexample or proof that no stronger invariant can work. A repair would need a capture-incidence validity clause and its native initialization/maintenance bridge; no stronger premise was silently substituted into the target.

`Computed.rowInput caller` satisfies `RowsValid` without added assumptions, proved in `computed_rowInput_valid`. The failed universal preservation result cannot be applied to its three-step `row_bound_produced` prefix. No preservation claim is made for that example.

## Actual checks and retained diagnostics

- Initial focused build: `lake build +YulangClosure.OriginalExtrusionRowValidityR283`, exit 0; 13/13 jobs built in 18.4s (import cache was preserved).
- Initial direct check: `lake env lean -j1 -M1024 YulangClosure/OriginalExtrusionRowValidityR283.lean`, exit 1. `decide` with a free `caller` could not close the two computed-output goals; then `decide +revert` could not synthesize a Decidable universal caller quantifier. A genuinely concrete `gapCaller` repaired the check. The first draft also selected a conjunction containing, rather than equal to, the pending Work clause and assumed an unavailable `Inhabited Request`; both were corrected without adding axioms or assumptions.
- Repaired direct check: same command, exit 0, no output.
- Final focused build: same build command, exit 0, 13/13 jobs, changed module 885ms.

## Full bundled checker output

Command (from repository root):

```sh
python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py \
  --project /home/momota1029/rust/yulang/notes/theory/lean \
  --lake /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake \
  --module YulangClosure.OriginalExtrusionRowValidityR283 \
  --theorem YulangClosure.OriginalExtrusionRowValidityR283.resultState_next \
  --theorem YulangClosure.OriginalExtrusionRowValidityR283.resultState_external \
  --theorem YulangClosure.OriginalExtrusionRowValidityR283.resultState_failed \
  --theorem YulangClosure.OriginalExtrusionRowValidityR283.captureGap_valid \
  --theorem YulangClosure.OriginalExtrusionRowValidityR283.captureGap_pending_bad \
  --theorem YulangClosure.OriginalExtrusionRowValidityR283.captureGap_effect_count \
  --theorem YulangClosure.OriginalExtrusionRowValidityR283.captureGap_step_invalid \
  --theorem YulangClosure.OriginalExtrusionRowValidityR283.step_preserves_rows_counterexample \
  --theorem YulangClosure.OriginalExtrusionRowValidityR283.runPrefix_preserves_rows_counterexample \
  --theorem YulangClosure.OriginalExtrusionRowValidityR283.computed_rowInput_valid \
  --timeout 300
```

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
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache build +YulangClosure.OriginalExtrusionRowValidityR283
Build completed successfully (13 jobs).
[exit 0]
cwd: /home/momota1029/rust/yulang/notes/theory/lean
$ /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache env lean -j1 -M1024 --root=/tmp/yulang-lean-audit-u11_8u1e /tmp/yulang-lean-audit-u11_8u1e/YulangProofAudit.lean
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionRowValidityR283.resultState_next
YulangClosure.OriginalExtrusionRowValidityR283.resultState_next : ∀ (s : YulangClosure.OriginalExtrusionWork.State),
  YulangClosure.OriginalExtrusionRowValidityR283.resultState (YulangClosure.OriginalExtrusionWork.Result.next s) = s
'YulangClosure.OriginalExtrusionRowValidityR283.resultState_next' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.OriginalExtrusionRowValidityR283.resultState_next
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionRowValidityR283.resultState_external
YulangClosure.OriginalExtrusionRowValidityR283.resultState_external : ∀ (s : YulangClosure.OriginalExtrusionWork.State)
  (call : YulangClosure.OriginalExtrusionWork.External),
  YulangClosure.OriginalExtrusionRowValidityR283.resultState
      (YulangClosure.OriginalExtrusionWork.Result.external s call) =
    s
'YulangClosure.OriginalExtrusionRowValidityR283.resultState_external' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.OriginalExtrusionRowValidityR283.resultState_external
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionRowValidityR283.resultState_failed
YulangClosure.OriginalExtrusionRowValidityR283.resultState_failed : ∀ (s : YulangClosure.OriginalExtrusionWork.State)
  (error : YulangClosure.OriginalExtrusionWork.Failure),
  YulangClosure.OriginalExtrusionRowValidityR283.resultState
      (YulangClosure.OriginalExtrusionWork.Result.failed s error) =
    s
'YulangClosure.OriginalExtrusionRowValidityR283.resultState_failed' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.OriginalExtrusionRowValidityR283.resultState_failed
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionRowValidityR283.captureGap_valid
YulangClosure.OriginalExtrusionRowValidityR283.captureGap_valid : ∀
  (caller : YulangClosure.NativeValueStructure.Request),
  YulangClosure.OriginalExtrusionRowValidityR283.RowsValid
    (YulangClosure.OriginalExtrusionRowValidityR283.captureGap caller)
'YulangClosure.OriginalExtrusionRowValidityR283.captureGap_valid' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionRowValidityR283.captureGap_valid
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionRowValidityR283.captureGap_pending_bad
YulangClosure.OriginalExtrusionRowValidityR283.captureGap_pending_bad : YulangClosure.OriginalExtrusionWork.Work.visit
    {
      endpoint :=
        YulangClosure.OriginalExtrusionWork.Endpoint.effect (YulangClosure.NativeMergeExpansion.Endpoint.row 99),
      polarity := YulangClosure.NativeMergeExpansion.Polarity.positive, target := 1 } ∈
  (YulangClosure.OriginalExtrusionRowValidityR283.resultState
      (YulangClosure.OriginalExtrusionWork.step YulangClosure.OriginalExtrusionWork.funded
        (YulangClosure.OriginalExtrusionRowValidityR283.captureGap
          YulangClosure.OriginalExtrusionRowValidityR283.gapCaller))).pendingBounds
'YulangClosure.OriginalExtrusionRowValidityR283.captureGap_pending_bad' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionRowValidityR283.captureGap_pending_bad
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionRowValidityR283.captureGap_effect_count
YulangClosure.OriginalExtrusionRowValidityR283.captureGap_effect_count : (YulangClosure.OriginalExtrusionRowValidityR283.resultState
        (YulangClosure.OriginalExtrusionWork.step YulangClosure.OriginalExtrusionWork.funded
          (YulangClosure.OriginalExtrusionRowValidityR283.captureGap
            YulangClosure.OriginalExtrusionRowValidityR283.gapCaller))).effects.length =
  2
'YulangClosure.OriginalExtrusionRowValidityR283.captureGap_effect_count' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionRowValidityR283.captureGap_effect_count
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionRowValidityR283.captureGap_step_invalid
YulangClosure.OriginalExtrusionRowValidityR283.captureGap_step_invalid : ¬YulangClosure.OriginalExtrusionRowValidityR283.RowsValid
    (YulangClosure.OriginalExtrusionRowValidityR283.resultState
      (YulangClosure.OriginalExtrusionWork.step YulangClosure.OriginalExtrusionWork.funded
        (YulangClosure.OriginalExtrusionRowValidityR283.captureGap
          YulangClosure.OriginalExtrusionRowValidityR283.gapCaller)))
'YulangClosure.OriginalExtrusionRowValidityR283.captureGap_step_invalid' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionRowValidityR283.captureGap_step_invalid
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionRowValidityR283.step_preserves_rows_counterexample
YulangClosure.OriginalExtrusionRowValidityR283.step_preserves_rows_counterexample : ¬YulangClosure.OriginalExtrusionRowValidityR283.StepPreservesRows
'YulangClosure.OriginalExtrusionRowValidityR283.step_preserves_rows_counterexample' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionRowValidityR283.step_preserves_rows_counterexample
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionRowValidityR283.runPrefix_preserves_rows_counterexample
YulangClosure.OriginalExtrusionRowValidityR283.runPrefix_preserves_rows_counterexample : ¬YulangClosure.OriginalExtrusionRowValidityR283.RunPrefixPreservesRows
'YulangClosure.OriginalExtrusionRowValidityR283.runPrefix_preserves_rows_counterexample' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionRowValidityR283.runPrefix_preserves_rows_counterexample
YULANG_AUDIT_BEGIN YulangClosure.OriginalExtrusionRowValidityR283.computed_rowInput_valid
YulangClosure.OriginalExtrusionRowValidityR283.computed_rowInput_valid : ∀
  (caller : YulangClosure.NativeValueStructure.Request),
  YulangClosure.OriginalExtrusionRowValidityR283.RowsValid
    (YulangClosure.OriginalExtrusionWork.Computed.rowInput caller)
'YulangClosure.OriginalExtrusionRowValidityR283.computed_rowInput_valid' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalExtrusionRowValidityR283.computed_rowInput_valid
[exit 0]
PASS: YulangClosure.OriginalExtrusionRowValidityR283.resultState_next, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionRowValidityR283.resultState_external, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionRowValidityR283.resultState_failed, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionRowValidityR283.captureGap_valid, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionRowValidityR283.captureGap_pending_bad, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionRowValidityR283.captureGap_effect_count, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionRowValidityR283.captureGap_step_invalid, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionRowValidityR283.step_preserves_rows_counterexample, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionRowValidityR283.runPrefix_preserves_rows_counterexample, under its printed hypotheses; axiom whitelist satisfied.
PASS: YulangClosure.OriginalExtrusionRowValidityR283.computed_rowInput_valid, under its printed hypotheses; axiom whitelist satisfied.
Named declarations only; ordinary-mistake check, not independent review or source correspondence.
```

The checker command exited 0. Its output above contains every delivered theorem's printed type and complete `#print axioms` result. The exact lists are: `resultState_next`, `resultState_external`, `resultState_failed`: none; `captureGap_valid`, `step_preserves_rows_counterexample`, `runPrefix_preserves_rows_counterexample`, `computed_rowInput_valid`: `[propext, Quot.sound]`; `captureGap_pending_bad`, `captureGap_effect_count`, `captureGap_step_invalid`: `[propext]`. No `Classical.choice` appears. A search of the new module for `sorry`, `admit`, project `axiom`, `debug.skipKernelTC` and `unsafe` produced no matches (`rg` exit 1).

## Application, omitted proof cases and first remaining premise

`StepPreservesRows` quantifies over every `Funding` and every `RowsValid` `State`; `RunPrefixPreservesRows` additionally quantifies over every fuel. Their negations are kernel accepted. The explicit counterexample uses `funded` and the `.visit` Work constructor; it refutes those universal propositions without needing to finish a case split. `WorkValid` itself covers `.visit`, `.function`, `.tuple`, `.record`, `.variant`, `.effectView`, `.bound`, and `.incomingAllowance`; `resultState` and its three audited equations cover `.next`, `.external` and `.failed`. Preservation for the other Work constructors, external-yield, failure and partial Cell publication before failure is **not proved**. In particular, the existing `Computed.post_publication_failure_retains_cells` is an operational equation, not a `RowsValid` preservation proof.

At the unchanged R70 edge, this establishes no preservation premise: the proposed invariant is refuted. The first repair premise is validity of each source row referenced by a `captures id` incidence read by `incomingJobs`, plus preservation of that clause as capture tables and canonical maps evolve. The separate first native/source bridge remains authentication that Rust's initialized and mutated capture tables satisfy the repaired invariant. Then the actual `step` Work/Result cases and fuel induction would still need proof. None of those is supplied by the model counterexample.

## Frozen artifact and STOP

- Lean source SHA-256: `31c83006c8d9b411b00d045fd16c9e5875e8a73d5baead989c7a55315f3a3f10`.
- Exact writes: this Lean module, this inbox handoff, and generated files under the leased `.lake/build`. Existing cache was preserved. No Rust, other Lean source, config, dependency, test, Git, or scheduling write.
- No descendants, background child or continuing Lean/Lake process. All invoked processes returned an exit status. No independent review, native correspondence, or production authority is claimed.
- Packet allocation: 1,800s maximum, no renewal. The first explicit clock sample was 2026-11-02 18:49:55 UTC; the final STOP instant and inbox hash are supplied to the primary in the frozen handoff message. Earlier start telemetry is unavailable, so no fabricated exact active-work duration is claimed. Reserve the full 1,800s until primary runtime accounting reconciles the actual charge.
- **STOP: all writes cease after this handoff is frozen.**

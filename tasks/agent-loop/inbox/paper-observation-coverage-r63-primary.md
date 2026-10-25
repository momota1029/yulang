# R63 primary verification receipt — revision 1

Sprint `YULANG3-VIEW-OBSERVATION-COVERAGE-20261026/r63`, contract r2 SHA-256 `aaeeaab87c69626d9299b99783f11eabe4c31fd5c99703eedf647af6fc5507f9`; baseline `93d08d5867015741b3588ea3df4c56903b2bbe83`; branch `yulang3`. Primary `/root`; live UUID/effective model/effort and exact active-work duration UNKNOWN. Worker `/root/r63_view_coverage_proof` is STOPPED; its handoff r1 SHA-256 `5857db1f531e6774c66973a6ee998d065f762655c4c6b02b419ef825b3e40cbe`.

## Disposition

**Primary verification PASS for the four fixed represented theorems. Fresh independent review and adjudication remain pending.** The worker's audit process failure remains preserved as a failure: its audit exited 1 on unsupported `pp.width`; its four printed declarations were complete and the unchanged `validate_audit` accepted the complete capture. The primary ran its own one-shot complete audit against the byte-identical candidate using a verifier-owned audit input without that unsupported option. Primary audit exited 0 and `validate_audit` passed. This is the separately budgeted primary execution, not a retry or repair of the worker's run. No integration or parent-gate closure is claimed here.

## Frozen inputs and artifact identity

Primary independently checked all 30 source pins against baseline commit bytes: **30/30 MATCH**. Recursive source enumeration from `PaperObservationCoverage` found exactly 22 internal `YulangClosure` modules. A static scan of that complete cone for `sorry`, `admit`, project `axiom`, `unsafe`, `native_decide`, `implemented_by`, or `run_tac` found zero matches. The candidate SHA-256 is `ffbef4f87b61396258a693e7a091a767c5610efbd9128024ddf108c0348c82d2`; the primary detached worktree has the exact baseline root and candidate only, with no root import change.

Worker frozen evidence independently rehashed against its handoff: candidate `ffbef4f87b61396258a693e7a091a767c5610efbd9128024ddf108c0348c82d2`; worker audit `077493832b4bc9e67a57796ec77aaaddf9133df88b3fc4fc05baad582ae3e804`; runner `b6dd46a4f39c928e00293e555f8bb931b8bafb9462e7720a894342aed0cd199a`; worker process manifest `22c178c2eb5663015868ada421e52220dd3ccce6e746dbc417aea81b94dc1490`; proof checks `77d5ca2ac68377c4b766d30c3526b6e1902c63ff648e22b63a320ff57373a841`. All four worker call captures match their process-manifest lengths and hashes. Worker call exits are `0, 0, 0, 1`, elapsed `0.465871340, 0.114888528, 47.223224017, 2.220752021` seconds, total `50.024735906`; no timeout or retry. The worker's failure output and audit source remain unchanged.

Primary candidate SHA matches the worker candidate. Primary audit SHA-256 `72c6da74698f47871fba03da7d9ad15cc7e07dbceeb8028bfa09e84bcef2efb6` differs only by removing the unsupported `set_option pp.width 120`; no candidate declaration or expected name/type/audit logic was changed. Primary runner SHA-256 `b6dd46a4f39c928e00293e555f8bb931b8bafb9462e7720a894342aed0cd199a`. Primary process-manifest SHA-256 `84d9cfa84092e15cd9d68dc39ef7ab3bab79010a2800e021906625113ec66e8b`. Primary cache: 176 files, sorted relative-path/SHA256 listing digest `d8b48879a5df6ce2f7e5cfb8ac8370417f72d2a7a4f57f078410827fbb2c3843`.

The four exact primary calls used the resolved native Lake executable SHA-256 `8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1`, Lean 4.35.0, serial `-j1 -M1024`, with the pinned project manifest and isolated cache. Each process exited 0, without signal or timeout; exact argv, effective environments, PIDs, monotonic timings and capture hashes are in the primary process manifest. Total checker time: **44.813585921 / 150 seconds**. One focused build only; no tests, Cargo, network, installation/update, or full default build.

| Call | Command | Exit | Elapsed seconds | Capture SHA-256 (stdout / stderr) |
|---|---|---:|---:|---|
| 1 | resolved Lake `--version` | 0 | 0.064729417 | `165f92ed239a8c7db772bf5ee9d58c59357b489951582a12c86dc9d8e06b23a2` / `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| 2 | `lake env lean --version` | 0 | 0.115501348 | `eb22144228dd41cd51a0c84af4f976cd0cef473102dcf99b60be756b11f2b95a` / `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| 3 | focused `+YulangClosure.PaperObservationCoverage` build | 0 | 44.017415102 | `e47fd125495b21b3ea50def8ee5f335ed4f93aead456f75a71af647d9f1bc006` / `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| 4 | complete primary audit `.lake/R63Audit.lean` | 0 | 0.615940054 | `08d379b8ba1aef4d38f2c9cfed3260815708ce5cb2aa1b78aeb41b62de6a1cb9` / `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |

Complete build output has 23/23 jobs successful, 692 warning entries from pinned imported modules, zero candidate warnings. The captured audit output contains exactly four candidate module theorem constants, exact complete types and axiom reports, and 4/4 terminal module count. The bundled repository `check_lean.py::validate_audit` passed on the full call-04 stdout+stderr with the four declaration names independently enumerated from the frozen candidate and contract. Separate exact-name/kind/count validation passed. The complete primary stdout is included below byte-for-byte.

## Theorem assessment under the printed hypotheses

1. `view_operand_force_typed` proves the exact closed term `force (view metadata (delay (ret (literal unit))))` has type base-unit for arbitrary `d : DeclarationTable` and arbitrary view metadata, with empty graph and type environments. The arbitrary declaration table is intentional because that is the judgment's structure-valued first index; the term contains no free term or type variable and requires no declaration entry.
2. `no_observation_step_from_view` quantifies arbitrary heap, metadata, wrapped value and target. Inspection of the exact `ObservationStep` constructors shows graph-read starts only from graph-reference, direct type-beta cannot reduce a view, and the type-application lift cannot start from a top-level view. No step exists.
3. `view_operand_no_literal_delay_trace` quantifies arbitrary heap, metadata and body. The zero-step constructor requires equality of the distinct view and delay constructors; every nonempty trace would require the impossible first step from a view. Thus the literal wrapped delay is unreachable for any heap, including the exact allocated heap required by R62.
4. `connected_executor_view_force_stuck` quantifies arbitrary declaration table, binder, metadata and body, at the fixed empty stack. Its equality is the actual existing `PaperExtendedExecution.controlStep` result, reducing to `none` by `rfl`; no represented transition was added.

The typing witness plus absent observation path falsifies the unqualified finite-observation coverage premise for represented terms. It does not refute R62's conditional theorem, prove compiler emission of this exact term, mean the paper machine returns Bad, establish nontermination or a production defect, or prove full evaluation safety. View metadata remains intact. No view transition, erasure, source restriction or semantic edit was introduced. The paper's view and canonical-form clauses are cited in the frozen contract; whole-language, source/native, R23, inference A/B and production obligations remain OPEN.

## Complete primary audit stdout

```text
YULANG_DECL_KIND YulangClosure.PaperTypes.PaperObservationCoverage.view_operand_force_typed theorem
YULANG_DECL_KIND YulangClosure.PaperTypes.PaperObservationCoverage.no_observation_step_from_view theorem
YULANG_DECL_KIND YulangClosure.PaperTypes.PaperObservationCoverage.view_operand_no_literal_delay_trace theorem
YULANG_DECL_KIND YulangClosure.PaperTypes.PaperObservationCoverage.connected_executor_view_force_stuck theorem
YULANG_MODULE_DECLARATIONS 4/4
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperObservationCoverage.view_operand_force_typed
YulangClosure.PaperTypes.PaperObservationCoverage.view_operand_force_typed : ∀
  (d : YulangClosure.PaperTypes.DeclarationTable) (metadata : YulangClosure.PaperTypes.ViewMetadata),
  YulangClosure.PaperTypes.PaperComputationTyped d (@List.nil (Prod Nat YulangClosure.PaperTypes.Ty))
    (@List.nil YulangClosure.PaperTypes.Ty)
    (YulangClosure.PaperTypes.Computation.force
      (YulangClosure.PaperTypes.Value.view metadata
        (YulangClosure.PaperTypes.Value.delay
          (YulangClosure.PaperTypes.Computation.ret
            (YulangClosure.PaperTypes.Value.literal YulangClosure.PaperTypes.Literal.unit)))))
    (YulangClosure.PaperTypes.Ty.base YulangClosure.PaperTypes.Base.unit)
'YulangClosure.PaperTypes.PaperObservationCoverage.view_operand_force_typed' does not depend on any axioms
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperObservationCoverage.view_operand_force_typed
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperObservationCoverage.no_observation_step_from_view
@YulangClosure.PaperTypes.PaperObservationCoverage.no_observation_step_from_view : ∀
  {heap : YulangClosure.PaperTypes.FreshHeap.Heap} {metadata : YulangClosure.PaperTypes.ViewMetadata}
  {value target : YulangClosure.PaperTypes.Value},
  Not
    (YulangClosure.PaperTypes.PaperHeapObservation.ObservationStep heap
      (YulangClosure.PaperTypes.Value.view metadata value) target)
'YulangClosure.PaperTypes.PaperObservationCoverage.no_observation_step_from_view' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperObservationCoverage.no_observation_step_from_view
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperObservationCoverage.view_operand_no_literal_delay_trace
@YulangClosure.PaperTypes.PaperObservationCoverage.view_operand_no_literal_delay_trace : ∀
  {heap : YulangClosure.PaperTypes.FreshHeap.Heap} {metadata : YulangClosure.PaperTypes.ViewMetadata}
  {body : YulangClosure.PaperTypes.Computation},
  Not
    (YulangClosure.PaperTypes.PaperHeapObservation.ObservationTrace heap
      (YulangClosure.PaperTypes.Value.view metadata (YulangClosure.PaperTypes.Value.delay body))
      (YulangClosure.PaperTypes.Value.delay body))
'YulangClosure.PaperTypes.PaperObservationCoverage.view_operand_no_literal_delay_trace' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperObservationCoverage.view_operand_no_literal_delay_trace
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperObservationCoverage.connected_executor_view_force_stuck
YulangClosure.PaperTypes.PaperObservationCoverage.connected_executor_view_force_stuck : ∀
  (d : YulangClosure.PaperTypes.DeclarationTable) (binder : YulangClosure.PaperTypes.TermName)
  (metadata : YulangClosure.PaperTypes.ViewMetadata) (body : YulangClosure.PaperTypes.Computation),
  @Eq (Option YulangClosure.PaperTypes.PaperCoreControl.State)
    (YulangClosure.PaperTypes.PaperExtendedExecution.controlStep d binder
      {
        head :=
          YulangClosure.PaperTypes.Computation.force
            (YulangClosure.PaperTypes.Value.view metadata (YulangClosure.PaperTypes.Value.delay body)),
        stack := @List.nil YulangClosure.PaperTypes.Computation })
    (@Option.none YulangClosure.PaperTypes.PaperCoreControl.State)
'YulangClosure.PaperTypes.PaperObservationCoverage.connected_executor_view_force_stuck' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperObservationCoverage.connected_executor_view_force_stuck
```

## Cessation and next gate

All four primary checker processes have exited; no primary process or descendant remains. The primary candidate, audit, runner, manifest, cache and four capture pairs are frozen. Request a fresh non-author `compiler_referee` review on the fixed contract, worker handoff/failure, primary artifacts/output and this receipt. Keep the exact review lease to `tasks/agent-loop/inbox/paper-observation-coverage-r63-review.md`, zero checker calls. Do not integrate or adjudicate the coverage gate before that review returns.

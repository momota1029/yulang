# R63 rebuild proof handoff — revision 1

Sprint `YULANG3-VIEW-OBSERVATION-COVERAGE-REBUILD-20261026/r1`; governing contract revision r2 SHA-256 `909068e6aebc834ae4d6f99b8055f5448dbe26c914c9c71f1e51f81aae001cd9`. Original R63 contract r2 SHA-256 `aaeeaab87c69626d9299b99783f11eabe4c31fd5c99703eedf647af6fc5507f9`. Frozen proof baseline `93d08d5867015741b3588ea3df4c56903b2bbe83`; branch `yulang3`.

Assignment `/root/r63_rebuild_proof`; registered `lean_prover`, no contributing descendants. Session UUID, effective runtime model/effort, requested concrete model/effort and exact total active-work duration **UNKNOWN**. Active-work/resume receipts sent to primary; r1 paused before writes/checkers for explicit `.lake/build` lease, then same live handle resumed under r2. No budget reset or retry. This is a fresh candidate with four kernel-accepted theorem declarations and successful complete audit; independent review, primary acceptance, source/native correspondence and production authority remain unestablished.

## Source and parent correspondence

Read original `docs/yulang-operational-type-safety-ja.tex`: source-correspondence correction :54–63; values :137–164; typing :215–228; machine/value observation :256–270 and :299–327; canonical forms :995–1008 (especially :998–1005); progress :1117–1137; precise simulation :1860–1877. Manuscript SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`. Constructor or explicit view evidence is admitted; administrative view projection appears in the paper. Read corrected candidate `notes/theory/2026-10-24-corrected-core-value-continuation.md` V1/V2/V5/V6 and corrected-machine simulation/source-bridge scope. These research drafts establish no additional semantic authority or concrete Lean instance.

Read original parent `YulangClosure.PaperTypes.PaperHeapExecution.allocated_force_control` and its actual dependencies. It requires `PaperHeapObservation.ObservationTrace (allocate b rho heap) source (.delay body)` on the exact allocated heap; declaration table, graph, target environment, body, stack and result remain shared. Read retained R63 worker failure/primary receipt and R62 review; no old PASS was used as this candidate's validation.

All 30 original contract pins matched before construction and at freeze. The prebuilt workspace contains only `notes/theory/lean`: 26 copied source/project files were checked directly and four uncopied sources against read-only exact baseline Git blobs. First read-only pin script exited 1 on `FileNotFoundError` for absent copied `docs/yulang-operational-type-safety-ja.tex`; it wrote nothing and made no checker call. Corrected source selection matched 30/30. Native Lake was resolved by read-only `elan which lake`, exit 0, SHA-256 `8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1`.

## Frozen output paths and hashes

Workspace `/tmp/yulang-r63-rebuild-20261026/proof`. Changed candidate only at `notes/theory/lean/YulangClosure/PaperObservationCoverage.lean`; no root import or frozen source/config/dependency file changed. Scratch audit, runner, manifest, checks and captures are exact leased paths below. Generated `.lake/build` is the leased symlink to `/tmp/yulang-r63-rebuild-20261026/proof/lake-build`; cache has 176 files, sorted `SHA256  relative-path` listing digest `ce4da709f726dc5f703fca67e296f4abcde1649d1f00f8687871bca65e3bf958` (final newline). Complete cache listing, 30 pins and all 22 recursive internal module hashes are retained in `proof-checks.txt`.

| Relative path | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/PaperObservationCoverage.lean` | `e2707b5387c85175948c24d3d4dd225473e796e42e7a8c5fdd5160618cd24dd0` |
| `notes/theory/lean/.lake/R63RebuildAudit.lean` | `daaa660498e7c77d16075072bd06f829a2a5cebb04b2ea1fead38fb6963ec9a3` |
| `run_call.py` | `e56fd92ca207abde16d0ac5b20778d739a7e879e3ac49498b01b0769dfdcc0e7` |
| `process-manifest.json` | `1b22c39fb6814c2c8f721de2decc828af26025f2f0dd11ac9bd235f1b09da4c0` |
| `proof-checks.txt` | `7f936a066cecb7b8e588bc01bba6a61532c1d5c0e5d2343233c631019e10733d` |
| `call-01.stdout` | `165f92ed239a8c7db772bf5ee9d58c59357b489951582a12c86dc9d8e06b23a2` |
| `call-01.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `call-02.stdout` | `eb22144228dd41cd51a0c84af4f976cd0cef473102dcf99b60be756b11f2b95a` |
| `call-02.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `call-03.stdout` | `156b7318380a6f858e932e06bd67604b870759c5d117cfa67d569e728f498538` |
| `call-03.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `call-04.stdout` | `08d379b8ba1aef4d38f2c9cfed3260815708ce5cb2aa1b78aeb41b62de6a1cb9` |
| `call-04.stderr` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |

Full internal import cone: **22 modules**. Static scan of every full source found **zero** matches for holes, project axioms, `unsafe`, `native_decide`, `implemented_by`, `run_tac`, kernel skipping or trust-level bypass. This static result complements each actual transitive axiom audit; it is not independent proof review.

## Fresh execution evidence

Pinned toolchain `leanprover/lean4:v4.35.0`; no external Lake packages. Actual outputs:

```text
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

Exactly four literal checker calls, all exit 0; no signal, timeout or retry. Total checker elapsed **43.802823876/150 seconds**, each <=120 seconds. Runner sets `LEAN_NUM_THREADS=1`; project and audit use `-j1 -M1024`. Manifest retains argv, cwd, selected effective environment, PID, Unix/monotonic start, elapsed time, cap, exits, capture lengths and hashes. No tests, Cargo, network, install/update, full default build, root import or semantic edits occurred.

| Call | Literal argv | Exit | Elapsed seconds |
|---|---|---:|---:|
| 1 | `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --version` | 0 | 0.414617713 |
| 2 | `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean --version` | 0 | 0.114377512 |
| 3 | `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache build +YulangClosure.PaperObservationCoverage` | 0 | 40.804256783 |
| 4 | `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache env lean -j1 -M1024 --root=. .lake/R63RebuildAudit.lean` | 0 | 2.469571868 |

Focused build completed 23 jobs; 692 warning entries from pinned imports, 0 candidate warnings; full 456163-byte output retained. Full call-04 stdout+stderr passed unchanged bundled `check_lean.py::validate_audit`, with names independently enumerated from candidate source; module-origin name/kind/count enumeration is exactly four theorem declarations, 4/4. Captures rehashed against manifest. No audit option error occurred.

## Complete types and axioms

Unedited full call-04 stdout follows; stderr empty:

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

`view_operand_force_typed`: no axioms. Each of `no_observation_step_from_view`, `view_operand_no_literal_delay_trace`, `connected_executor_view_force_stuck`: `[propext, Quot.sound]`. No `sorryAx`, project axiom or native-evaluation assumption is reported.

## Coverage and exact parent application

The closed witness uses Literal(unit), Ret, Delay, View and Force introduction under empty graph/type environments, arbitrary `DeclarationTable`, arbitrary preserved metadata and no typing hypothesis. The no-step result quantifies arbitrary heap/metadata/wrapped value/target and eliminates all three frozen observation constructors: graph-read and type-application lift have different source constructors; direct type beta returns none on View. No-trace quantifies arbitrary heap/metadata/body: distinct View/Delay constructors rule out reflexivity, and a nonempty trace needs the impossible first step. Existing connected executor returns none for arbitrary declaration table/binder/metadata/body at the fixed empty stack by definitional equality.

Apply with `body := .ret (.literal .unit)` and `source := .view metadata (.delay body)`. The force is closed and typed; no trace reaches the same literal `.delay body` for **any** heap, including the exact `allocate b rho heap` required by `allocated_force_control`. Thus closed represented typing alone cannot supply the unqualified universal finite constructor-observation premise. R62's conditional theorem remains valid; its path premise is absent. `none` denotes no implemented transition here, not paper `Bad`, nontermination, a source-qualified compiler emission claim or a production semantic defect.

Represented constructors remain intact and metadata is never erased. No extra hypothesis, view transition, expose rule, altered typing, reduced source domain or fresh witness replaces a required shared witness. Omitted/open: graph canonical forms and guard termination, full view execution semantics, arbitrary stack progress, whole-language execution safety, actual source elaboration/compiler emission, native correspondence, R23, inference A/B and production.

First remaining premise: **R62-FINITE-CONSTRUCTOR-OBSERVATION-1**, owner **primary source/proof intake**. It needs source-qualified constructor/View observation and actual source-to-observation/executor correspondence respecting explicit views, or a separately reviewed and authorized reformulation. Existing owners `PaperHeapObservation.ObservationStep` and `PaperExtendedExecution.controlStep` expose the gap; this packet grants no rule change. Source -> generated constraints -> propagation -> consumer/native correspondence is omitted and OPEN; no Rust slice is leased.

## Cessation

**STOPPED / writes stopped.** All four checker processes and runner exited; no descendants or continuing processes remain. Candidate, audit, runner, manifest, checks, captures, cache and build symlink are frozen. This single shared handoff is the final write. Primary owns verification/review assignment, adjudication, shared status, integration and Git. Commit-ready/independent-review status: **PENDING**.

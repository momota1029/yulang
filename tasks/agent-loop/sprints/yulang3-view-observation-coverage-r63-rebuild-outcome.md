# R63 rebuild outcome — accepted bounded represented research result

Sprint: `YULANG3-VIEW-OBSERVATION-COVERAGE-REBUILD-20261026/r1`  
Contract revision: r2; SHA-256 `909068e6aebc834ae4d6f99b8055f5448dbe26c914c9c71f1e51f81aae001cd9`  
Proof baseline: `93d08d5867015741b3588ea3df4c56903b2bbe83`  
Coordination baseline: `43473afa61a5fd7853635e134b3d40db125ec71d`  

## Primary adjudication

**CLEAN accepted for the four represented declarations and their bounded conclusion.** The candidate establishes that represented closed typing alone does not supply R62's unqualified finite observation premise on the same allocated heap. The existing connected executor returns `none` for the specified empty-stack view-force state under the frozen represented definitions.

The original four public declarations, quantifiers and witness are preserved. `view_operand_force_typed` reports no axioms; each of `no_observation_step_from_view`, `view_operand_no_literal_delay_trace`, and `connected_executor_view_force_stuck` reports `[propext, Quot.sound]`. Primary independently verified the complete audit and exact names/kinds/count. The fresh non-author `compiler_referee` review is CLEAN with no blocking, major or minor correctness findings.

This is an accepted represented auxiliary-relation result. It does not refute R62's conditional theorem, establish source compiler emission of the witness, identify paper `Bad`, prove nontermination, establish source/native correspondence or whole-language safety, or establish a production defect. `R62-FINITE-CONSTRUCTOR-OBSERVATION-1`, R23, source/native correspondence, inference A/B, whole-language safety and production remain **OPEN**. Source integration is **NOT AUTHORIZED / NOT PERFORMED**. No repository Lean source, root import, Rust code, test, fixture or expected output changed in this sprint.

## Frozen evidence and verification

- Candidate SHA-256: `e2707b5387c85175948c24d3d4dd225473e796e42e7a8c5fdd5160618cd24dd0`; complete candidate bytes are appended below so the new artifact remains reviewable if `/tmp` is later cleared.
- Proof handoff: `tasks/agent-loop/inbox/paper-observation-coverage-r63-rebuild.md`, SHA-256 `2cbd4f3dae1977c513e8e2ddf5993d5ffc3e0b37ffef4eb322b56fb88ff36c4a`.
- Primary verification: `tasks/agent-loop/inbox/paper-observation-coverage-r63-rebuild-primary.md`, SHA-256 `690e102e9acf21697aa49e5cb14633a3c0b58b5e840a4d04822c0b32ae564289`.
- Independent review, delivered by reviewer response and preserved by primary: `tasks/agent-loop/inbox/paper-observation-coverage-r63-rebuild-review.md`, SHA-256 `19bd0ea06409adb49b6bfa73cfc7d5a08cd811435f62ad958036bb35d0f1cba6`. Review author `/root/r63_rebuild_review`; primary is recorder. Reviewer made zero checker calls and no filesystem writes. Response-based delivery followed the repository handoff protocol; the review path lease transferred to primary only after response receipt. The body is preserved verbatim after its provenance header.
- Candidate matched across author and primary workspaces. The exact audit source hash is `daaa660498e7c77d16075072bd06f829a2a5cebb04b2ea1fead38fb6963ec9a3`.
- All 30 frozen input pins matched Git baseline and copied Lean sources. The recursive internal cone has 22 modules and the static scan found no holes, project axioms or scanned bypasses.
- Proof owner: four calls, all exit 0, total 43.802823876 checker seconds. Primary: four calls, all exit 0, total 39.386170623 checker seconds. Both captured manifests match stdout/stderr lengths and hashes; no retries, timeouts or signals. The complete primary audit stdout SHA-256 is `08d379b8ba1aef4d38f2c9cfed3260815708ce5cb2aa1b78aeb41b62de6a1cb9`; bundled `validate_audit` and exact declaration enumeration pass 4/4. Lean 4.35.0; Lake 5.0.0. Reviewer: zero checker calls.
- The original R63 worker's `pp.width` audit failure (exit 1) and loss of its isolated scratch artifacts remain historical evidence and are not converted into success. The rebuilt candidate has its own complete audit, primary verification and review.

## Coordination corrections and cessation

The first review dispatch contained a mistyped contract hash; contract bytes, `current.json` and both earlier receipts agree on the digest recorded above. The end selector's candidate hash response omitted its trailing `0`; primary recomputed both workspaces and confirms the full candidate hash above. Neither transcription error reflects an artifact mismatch. A primary pin-check script attempt also aborted before any write or checker call because it formed an incomplete path to a copied Lean source; the corrected independent check passed all 30 pins. Compact `current.json` edits initially exceeded the state-size limit; the shortened snapshot passes `python3 tools/agent_sprint.py check`, which is static scheduling evidence only.

Proof worker and reviewer are STOPPED; primary checker processes and runner exited. No descendants or continuing checker processes remain. Runtime model/effort/session UUID and exact active durations are UNKNOWN where not evidenced. All old reviewer and eight legacy UNKNOWN reservations remain quarantined. New candidate, handoffs, receipts and scratch evidence remain frozen; no deletion, source integration, commit or push was performed.

## Complete candidate bytes

The following fenced block is copied from the frozen candidate file whose SHA-256 is recorded above:

```lean
import YulangClosure.PaperHeapExecution

/-! A represented obstruction to deriving finite literal-constructor observation
from closed typing alone. No view execution rule or source correspondence is
asserted. R62 remains conditional on its literal finite observation premise. -/
namespace YulangClosure.PaperTypes.PaperObservationCoverage

open FreshHeap PaperHeapObservation PaperCoreControl

/-- The closed force witness retains arbitrary view metadata. -/
theorem view_operand_force_typed (d : DeclarationTable) (metadata : ViewMetadata) :
    PaperComputationTyped d [] []
      (.force (.view metadata (.delay (.ret (.literal .unit))))) (.base .unit) :=
  .force (.view (.delay (.ret .literal)))

/-- No frozen observation constructor starts from a top-level view. -/
theorem no_observation_step_from_view
    {heap : Heap} {metadata : ViewMetadata} {value target : Value} :
    ¬ ObservationStep heap (.view metadata value) target := by
  intro step
  cases step with
  | typeBeta beta => simp [PaperTypeBetaExecution.typeBetaValue] at beta

/-- Even the wrapped literal delay cannot be reached from the view. -/
theorem view_operand_no_literal_delay_trace
    {heap : Heap} {metadata : ViewMetadata} {body : Computation} :
    ¬ ObservationTrace heap (.view metadata (.delay body)) (.delay body) := by
  intro trace
  cases trace with
  | cons first _ => exact no_observation_step_from_view first

/-- The unchanged connected executor has no branch for this empty-stack state. -/
theorem connected_executor_view_force_stuck (d : DeclarationTable) (binder : TermName)
    (metadata : ViewMetadata) (body : Computation) :
    PaperExtendedExecution.controlStep d binder
      ⟨.force (.view metadata (.delay body)), []⟩ = none := by
  rfl

end YulangClosure.PaperTypes.PaperObservationCoverage

```

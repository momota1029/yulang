# Sprint R299 — imported provider schemes in the candidate inference world

Status: CHECKPOINTED_UNREVIEWED, solo serial primary; no independent review or theorem closure is claimed.
Branch / baseline commit: `research/simple-sub-intrusion` / `e0b6081b4`.
Authority: unchanged R149 Types/Console behavior; unified design §§4.1–4.5, 7.1, 9 stages 2/4/6; proof companion §§7.1–7.2 and 7.5. R298 exact role implementation-source inventory is a prerequisite only.
Primary approval: the user's persistent implementation-and-proof goal. The user explicitly requires solo work; no child agent or dispatcher process is started.

## Parent outcome and success evidence

Parent remains Authoritative R149: unchanged Types and Console source bytes, public types, ordered host output and runtime behavior. R149, source/native soundness, principality and production remain OPEN.

This sprint connects one authenticated imported binding's source declaration and provider candidate scheme to the importing candidate solve, with each imported use instantiated through that importing solve's existing graph/FreshUse machinery. The imported scheme must retain source identity, local quantified rows and any unresolved source-role obligations. Provider and consumer facts must participate in the same `InferenceSession`; independently inferring a closed `yu-types` scheme and re-running an unrelated solver is outside the approved design.

The first success case is a small imported function whose provider and consumer HIRs have distinct artifact-branded roots. Evidence must show the imported name joins to the exact public provider binding, its provider graph contributes constraints to the consumer solve, and two imported uses retain separate local rows while preserving shared anchors. A negative control must reject missing, ambiguous, stale, or mismatched provider ownership without falling back to spelling.

## Work and boundaries

- Trace the exact import identity from `SourceImportId` through `LocalSourceResolution::Imported`, provider binding ownership, collected source roots, candidate graph capture, and the existing FreshUse route.
- Implement the smallest multi-module candidate-world bridge that keeps provider and consumer constraints in one candidate session. Preserve artifact-branded source roots; do not concatenate HIR IDs or reconstruct identity from names.
- Carry a provider's retained candidate graph and source-role prerequisites into the consumer graph. Discharge no role until an actual receiver type and exact implementation target are available.
- Keep candidate-only / research status. Do not expose public schemes, add spelling-based intrinsic handling, select a role by inventory order, narrow R149, or claim full inference correctness.
- If the current `ConstraintBatch` ownership cannot safely host multiple HIR artifacts without a new authority decision, stop at the precise invariant and report the smallest missing design choice; do not substitute a disconnected closed-scheme solver.

## Exact write leases

- `crates/yu-hir/src/module.rs`
- `crates/yu-solver/src/lib.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `crates/yu-solver/src/candidate_source.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `tools/inference-playground/src/lib.rs`
- this sprint contract, `notes/theory/2026-10-22-r299-imported-scheme-same-world.md`, and Luna-owned `tasks/agent-loop/current.json`

No worker is active. Legacy UNKNOWN identities and their quarantined board lease stay untouched. One primary process and one Cargo process at a time; 1800 seconds charged, no carryover, no background work.

## Evidence and falsifiers

Focused tests cover exact source owner lookup, one provider-to-consumer imported binding, FreshUse isolation across two uses, same-session ownership, and fail-closed identity cases. Run the relevant focused test and `cargo test -p yu-playground` only if the change remains within the ordinary resource envelope. Passing tests are implementation evidence only.

Falsify the result if provider/consumer HIR identity is conflated, the import can resolve to another same-spelled declaration, a provider bound is omitted, an imported use bypasses the existing FreshUse maps, unresolved role obligations are dropped, or a missing provider is accepted.

## R299 checkpoint

The owner trace confirms a single-HIR `ConstraintBatch`, one-HIR `InferenceSession`, and private artifact-token ownership for occurrences and definition roots. Flattening HIRs is invalid. Exact public binding export ownership and role implementation inventory already have source-key-authenticated lookup routes. The coherent next implementation packet is a candidate-only multi-HIR source world feeding one shared batch/session and dispatching ownership queries per artifact. No source code changed; this checkpoint narrows the implementation seam and does not claim the sprint outcome completed.

## Review and stop

Solo primary work has no independent review. Freeze the changed source correspondence and handoff for a fresh review when available. Keep the proof and R149 gates OPEN. Commit and push only a coherent checkpoint from the inspected baseline; keep the worktree clean. Stop at the precise cross-artifact or proof boundary if the same-session construction cannot be established safely.

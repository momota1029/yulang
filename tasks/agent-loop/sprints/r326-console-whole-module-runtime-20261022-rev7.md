# Sprint R326 — run unchanged Console through the whole-module source schedule

Revision 7 supersedes revision 6 only for the solver lease set and next diagnostic step. Revisions 1–6 remain unchanged historical contracts.

Status: ACTIVE, solo serial lane. R325 remains an unreviewed bounded result at `3a9aea751`; R149 and the parent goal stay open.
Baseline: `3a9aea751` on `research/simple-sub-intrusion`.
Authority: unchanged user goal and Authoritative `notes/design/2026-10-20-r149-types-console.md`, especially Proposed behavior §§2–7 and exact Console source/output row. Preserve source bytes, standard-library import identity, role/impl semantics, and the user correction that contravariant `[io]` means `[io,'e]`.
Dispatch: solo serial work is required; `next_action_selector` cannot run without subagents. No fictional independent review or proof receipt.

## Parent and bounded outcome

The parent is all unchanged Yulang2 playground samples through ordinary inference/execution, with implementation and source/native proofs. R325 established exact Types output `(42, Yulang)\n` through selected member/operator roots and one authenticated `out::write` response.

R326 adds a whole-module source schedule for the exact 92-byte Console source, source-authenticated two-segment `out::write` import resolution, selected provider expression projection, and ordered host event capture. The selected `println` source now lowers. A focused test verifies the selected operation's exact family/export/operation identities.

## Current solver blocker

The authenticated `Display` role identity is now preserved even when it arrives through an implicit prelude import, whose exact role identity has no ordinary name binding. Candidate capture carries source role prerequisites alongside matching `FieldTail` row identities. This is partial transport evidence; there is not yet evidence that the exact `Display` obligation selects its implementation in the unchanged Console path.

A temporary environment-only bypass was used for diagnosis and removed. The exact Console runtime still stops with `DeferredSelectionUnavailable`. Latest readback shows active `add` FieldTail receivers with no positive shape or bound frontier; the six candidate targets therefore remain unsupported at that receiver. Trace how the unchanged integer operands constrain the exact provider FreshUse and whether the `Display` prerequisite is joined to the correct selected member before implementing another dispatch step. Keep ambiguous, missing, recursive-prerequisite, incomplete-inventory, and unstable/negative-evidence cases unavailable. Do not weaken the `[io,'e]` interpretation or remove the role preflight gate.

Expected output remains `hello from Yulang\n` followed by `3\n`, concatenated by the CLI in source order. Tests are implementation evidence only; source/native adequacy, role principality, R149, and production remain open.

## Exact leases

- `tools/inference-playground/src/lib.rs`
- `tools/inference-playground/src/main.rs`
- `tools/inference-playground/src/runtime/program.rs`
- `tools/inference-playground/src/runtime/machine.rs`
- `crates/yu-hir/src/module.rs`
- `crates/yu-hir/src/module/local_source.rs`
- `crates/yu-hir/src/module/source_annotation.rs` (diagnostic-only lease; source code currently unchanged)
- `crates/yu-solver/src/candidate_source.rs`
- `crates/yu-solver/src/candidate_effect.rs` — retain exact authenticated role identity for implicit prelude imports.
- `crates/yu-solver/src/shadow_apply.rs`
- `crates/yu-solver/src/candidate_scheme.rs` — connect source role prerequisites, provider FreshUse rows, actual operand constraints and exact FieldTail selection, preserving fail-closed status until discharged.
- this contract, `notes/theory/2026-10-22-r326-console-whole-module-runtime.md`, and `tasks/agent-loop/current.json`

Lease-entry hashes for HIR and prior solver paths are preserved in current state and revisions 2–5. No other paths are writable. No subagents/background work, sample rewrite, expected-output change, blanket staging, or history rewrite. R326 cap remains 2400 seconds with no carryover.

## Verification

Run exact Console inference/runtime, focused identity/role/FreshUse tests, `cargo test -p yu-playground --lib`, `cargo check -p yu-playground`, sprint static check, sprint tooling tests, and `git diff --check`. Keep tests, theorem gates, review status, and production status distinct. Inspect the full outbound range before non-forced push.

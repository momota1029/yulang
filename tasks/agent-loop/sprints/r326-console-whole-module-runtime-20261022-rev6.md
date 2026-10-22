# Sprint R326 — run unchanged Console through the whole-module source schedule

Revision 6 supersedes revision 5 only for the exact role-obligation lease and next step. Revisions 1–5 remain unchanged historical contracts.

Status: ACTIVE, solo serial lane. R325 remains an unreviewed bounded result at `3a9aea751`; R149 and the parent goal stay open.
Baseline: `3a9aea751` on `research/simple-sub-intrusion`.
Authority: unchanged user goal and Authoritative `notes/design/2026-10-20-r149-types-console.md`, especially Proposed behavior §§2–7 and exact Console source/output row. Preserve source bytes, standard-library import identity, role/impl semantics, and the user correction that contravariant `[io]` means `[io,'e]`.
Dispatch: solo serial work is required; `next_action_selector` cannot run without subagents. No fictional independent review or proof receipt.

## Parent and bounded outcome

The parent is all unchanged Yulang2 playground samples through ordinary inference/execution, with implementation and source/native proofs. R325 established exact Types output `(42, Yulang)\n` through selected member/operator roots and one authenticated `out::write` response.

R326 adds a whole-module source schedule for the exact 92-byte Console source, source-authenticated two-segment `out::write` import resolution, selected provider expression projection, and ordered host event capture. The selected `println` source now lowers. A focused test verifies the selected operation's exact family/export/operation identities.

## Current role-resolution blocker

Normal inference now reaches `candidate_source::preflight_with_imports` on authentic `std::io::console.say`. It deliberately rejects retained `where 'a: Display` because source-role obligations have no type-directed discharge yet. The obligation is authenticated and retained by `candidate_register_source_role_obligation`, then its subject row is preserved through candidate FreshUse. However it remains metadata: `SourceRoleObligation.role_identity` is not used to authorize an implementation.

A temporary environment-only bypass was used for diagnosis and removed. It allowed candidate collection to continue, where `execute_candidate_field_tails` stopped with `DeferredSelectionUnavailable`: generic `value.show` still has an unresolved receiver in the provider template. Do not remove the preflight gate as a solution. Connect the authentic Display obligation, FreshUse subject row, provider FieldTail receiver, and uniquely applicable implementation; keep ambiguous, missing, recursive-prerequisite, incomplete-inventory, and unstable/negative-evidence cases unavailable. Then restore the exact sample through normal inference and runtime.

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
- `crates/yu-solver/src/shadow_apply.rs`
- `crates/yu-solver/src/candidate_scheme.rs` — connect source role prerequisites to FreshUse type rows and exact FieldTail selection, preserving fail-closed status until discharged.
- this contract, `notes/theory/2026-10-22-r326-console-whole-module-runtime.md`, and `tasks/agent-loop/current.json`

Lease-entry hashes for HIR and prior solver paths are preserved in current state and revisions 2–5. No other paths are writable. No subagents/background work, sample rewrite, expected-output change, blanket staging, or history rewrite. R326 cap remains 2400 seconds with no carryover.

## Verification

Run exact Console inference/runtime, focused identity/role/FreshUse tests, `cargo test -p yu-playground --lib`, `cargo check -p yu-playground`, sprint static check, sprint tooling tests, and `git diff --check`. Keep tests, theorem gates, review status, and production status distinct. Inspect the full outbound range before non-forced push.

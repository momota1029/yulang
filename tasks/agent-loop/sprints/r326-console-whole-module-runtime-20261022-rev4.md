# Sprint R326 — run unchanged Console through the whole-module source schedule

Revision 4 supersedes revision 3 only for the exact LocalSource lease and next step. Revisions 1–3 remain unchanged historical contracts.

Status: ACTIVE, solo serial lane. R325 remains an unreviewed bounded result at `3a9aea751`; this sprint does not close R149.
Baseline: `3a9aea751` on `research/simple-sub-intrusion`.
Authority: unchanged user goal and Authoritative `notes/design/2026-10-20-r149-types-console.md`, especially Goal, Proposed behavior §§3–7, and exact Console source/output row. Preserve original bytes and standard-library resolution; no injected `main`, source rewrite, spelling intrinsic, or effect weakening.
Dispatch: `next_action_selector` cannot run without a subagent; user explicitly requires solo work. Continue as Luna primary with no fictional independent proof/review receipt.

## Parent and bounded outcome

The parent remains all unchanged Yulang2 playground samples passing through ordinary inference and execution, with implementation and source/native proofs. R325 established exact Types output `(42, Yulang)\n` through candidate-selected member/operator roots and one authenticated `out::write` response. R149 still requires Types and Console, public inferred types, ordered output, and the matching module's accepted inference result.

R326 connects the exact 92-byte Console program to the existing whole-module source schedule without requiring a selected `DefId`. A module run visits actual expression/computation roots in source order, services only the exact authenticated `std::io::out::write` capability, and completes with ordered CLI output `hello from Yulang\n3\n`.

Success evidence: use the exact pinned Console bytes and SHA-256 `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`; candidate inference accepts; whole-module runtime returns both exact writes in order; CLI has an explicit whole-module mode; Types selected-definition behavior stays exact. A test pass is not a source/native or general semantic proof. Keep R149, source/native adequacy, principality, remaining samples, theorem closure, and production OPEN.

## Constructive path and current blocker

- Producer: candidate inference and `RuntimeProgram::from_candidate_world` retain exact imported definitions, infix providers, source schedule, and host-write operation identity.
- Consumer: module schedule execution visits real source roots in order and completes with unit only after each root completes.
- Host: reuse the exact `SourceOperationPathImport` capability and raw continuation template response. Capture validated strings once, respond with unit, and resume that continuation once. Other operations remain unhandled.
- Provider projection now includes imports from source expression roots. Selected pinned bindings resolve two-segment operation paths through exact imported family identities. A focused test confirms the `out::write` family and operation source identities match.
- Current blocker: selected `println` provider source still fails `lower_module_with_selected_local_source` with `StructuralProjection`. Trace the source-carrier formation failure and fix only the exact unsupported construct with preserved ownership and operation identity.
- Falsifiers: missing/reordered Console expression; output differs from `hello from Yulang\n` then `3\n`; nonmatching declaration/payload accepted; continuation resumed twice; fake entrypoint or rewritten source; selected-definition regression.
- Preserve the user correction that contravariant `[io]` means `[io,'e]`, so `[state]` is not rejected for that reason.

## Exact write leases

- `tools/inference-playground/src/lib.rs`
- `tools/inference-playground/src/main.rs`
- `tools/inference-playground/src/runtime/program.rs`
- `tools/inference-playground/src/runtime/machine.rs`
- `crates/yu-hir/src/module.rs`
- `crates/yu-hir/src/module/local_source.rs` — identify/fix the selected Console binding LocalSource structural projection.
- `crates/yu-solver/src/candidate_source.rs` — inspect/fix only if the admitted provider reaches candidate preflight.
- `crates/yu-solver/src/shadow_apply.rs` — preserve root context only if needed.
- this contract, `notes/theory/2026-10-22-r326-console-whole-module-runtime.md`, and `tasks/agent-loop/current.json`

The module.rs lease-entry hash is recorded in current state; revision-2 solver hashes remain recorded in revision 2. No other paths are writable. No subagents, background work, fixture/expected-output rewrite, blanket staging, or history rewrite. R325's 1222 seconds are closed; R326 has a 2400-second cap and no carryover.

## Verification and boundary

Run exact Console inference/runtime, the focused import/carrier tests, `cargo test -p yu-playground --lib`, `cargo check -p yu-playground`, sprint static check, sprint tooling tests, and `git diff --check`. Inspect the complete outbound range before any non-forced push. Do not claim R149 or a proof gate closed from tests.

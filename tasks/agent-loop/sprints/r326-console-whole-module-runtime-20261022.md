# Sprint R326 — run unchanged Console through the whole-module source schedule

Status: ACTIVE, solo serial lane. R325 is preserved as an unreviewed bounded result at `3a9aea751`; this sprint continues the unchanged Yulang2 samples goal and does not close R149.
Baseline: `3a9aea751` on `research/simple-sub-intrusion`.
Authority: unchanged user goal and Authoritative `notes/design/2026-10-20-r149-types-console.md`, especially Goal, Proposed behavior §§3–7, and the exact Console source/output row. Preserve original bytes and standard-library resolution; no injected `main`, source rewrite, spelling intrinsic, or effect weakening.
Dispatch: `next_action_selector` cannot run without a subagent; user explicitly requires solo work. Continue as Luna primary with no fictional independent proof/review receipt.

## Parent and bounded outcome

The parent remains all unchanged Yulang2 playground samples passing through ordinary inference and execution, with implementation and source/native proofs. R325 established the exact Types result `(42, Yulang)\n` through candidate-selected member/operator roots and one authenticated `out::write` response. R149 still requires Types and Console, public inferred types, ordered output, and the matching module's accepted inference result.

R326 connects the exact 92-byte Console program to the existing whole-module source schedule without requiring any selected `DefId`. Preserve the current selected-definition entrypoint. A module run visits the actual expression/computation roots in source order, services only the exact authenticated `std::io::out::write` capability, and completes with ordered CLI output `hello from Yulang\n3\n`.

Success evidence: a test uses the exact pinned Console bytes and SHA-256 `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`; candidate inference accepts; the whole-module runtime returns both exact writes in order; CLI has an explicit whole-module mode; Types selected-definition behavior stays exact. A test pass is not a source/native or general semantic proof. Keep R149, source/native adequacy, principality, all remaining samples, theorem closure, and production OPEN.

## Constructive path and falsifiers

- Producer: existing candidate inference and `RuntimeProgram::from_candidate_world` retain exact imported definitions, infix providers, source schedule, and host-write operation identity.
- Consumer: add a module-schedule entrypoint with no selected binding; preserve all schedule entries and source order. Completion of a whole module yields unit only after every scheduled root completes.
- Host: reuse the exact `SourceOperationPathImport`-derived capability and raw continuation template response from R325. Capture each validated string once, respond with unit, and resume that request's continuation once. Other operations remain unhandled errors.
- CLI: expose an explicit whole-module run option; do not change existing `--run DEFINITION` semantics.
- Falsifiers: a schedule omits/reorders either Console expression; host capture is not `hello from Yulang\n` then `3\n`; a nonmatching declaration/payload is accepted; one continuation can be resumed twice; source is rewritten or a fake entrypoint is injected; a selected-definition regression appears.
- Preserve the user correction that contravariant `[io]` means `[io,'e]`, so `[state]` is not rejected for that reason.

## Exact write leases

- `tools/inference-playground/src/lib.rs`
- `tools/inference-playground/src/main.rs`
- `tools/inference-playground/src/runtime/program.rs`
- `tools/inference-playground/src/runtime/machine.rs`
- this contract, `notes/theory/2026-10-22-r326-console-whole-module-runtime.md`, and `tasks/agent-loop/current.json`

All other paths are read-only. No subagents, background work, test fixture rewrite, expected-output change, blanket staging, or history rewrite. R325 budget was charged 1222 seconds and is closed; R326 cap is 2400 seconds, no carryover.

## Verification and boundary

Run the exact Console path through inference and runtime, focused host/whole-module tests, `cargo test -p yu-playground --lib`, `cargo check -p yu-playground`, sprint static check, sprint tooling tests, and `git diff --check`. Inspect the full outbound range before each non-forced push. Do not claim R149 or a proof gate closed from these checks.

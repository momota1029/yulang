# Sprint R326 — run unchanged Console through the whole-module source schedule

Contract revision 3 supersedes revision 2 only for the exact lease extension and next implementation step. Revisions 1 and 2 remain unchanged historical snapshots.

Status: ACTIVE, solo serial lane. R325 remains an unreviewed bounded result at `3a9aea751`; this sprint does not close R149.
Baseline: `3a9aea751` on `research/simple-sub-intrusion`.
Authority: unchanged user goal and Authoritative `notes/design/2026-10-20-r149-types-console.md`, especially Goal, Proposed behavior §§3–7, and exact Console source/output row. Preserve original bytes and standard-library resolution; no injected `main`, source rewrite, spelling intrinsic, or effect weakening.
Dispatch: `next_action_selector` cannot run without a subagent; user explicitly requires solo work. Continue as Luna primary with no fictional independent proof/review receipt.

## Parent and bounded outcome

The parent remains all unchanged Yulang2 playground samples passing through ordinary inference and execution, with implementation and source/native proofs. R325 established the exact Types result `(42, Yulang)\n` through candidate-selected member/operator roots and one authenticated `out::write` response. R149 still requires Types and Console, public inferred types, ordered output, and the matching module's accepted inference result.

R326 connects the exact 92-byte Console program to the existing whole-module source schedule without requiring a selected `DefId`. A module run visits actual expression/computation roots in source order, services only the exact authenticated `std::io::out::write` capability, and completes with ordered CLI output `hello from Yulang\n3\n`.

Success evidence: test the exact pinned Console bytes and SHA-256 `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`; candidate inference accepts; whole-module runtime returns both exact writes in order; CLI has an explicit whole-module mode; Types selected-definition behavior stays exact. A test pass is not a source/native or general semantic proof. Keep R149, source/native adequacy, principality, remaining samples, theorem closure, and production OPEN.

## Constructive path and falsifiers

- Producer: candidate inference and `RuntimeProgram::from_candidate_world` retain exact imported definitions, infix providers, source schedule, and host-write operation identity.
- Consumer: add a module-schedule entrypoint with no selected binding; preserve schedule entries and source order. Whole-module completion yields unit only after every scheduled root completes.
- Host: reuse the exact `SourceOperationPathImport`-derived capability and raw continuation template response from R325. Capture each validated string once, respond with unit, and resume that request's continuation once. Other operations remain unhandled errors.
- Import bridge: projected provider expressions retain their imported roots. For selected pinned bindings, resolve two-segment operation paths such as `out::write` through the exact selected-root import environment, preserving family and operation source identities. This extends the existing source-authenticated selected-operation path resolution; it does not infer identity from spelling alone.
- Falsifiers: a schedule omits/reorders either Console expression; host capture is not `hello from Yulang\n` then `3\n`; a nonmatching declaration/payload is accepted; one continuation resumes twice; source is rewritten or a fake entrypoint is injected; selected-definition behavior regresses.
- Preserve the user correction that contravariant `[io]` means `[io,'e]`, so `[state]` is not rejected for that reason.

## Exact write leases

- `tools/inference-playground/src/lib.rs`
- `tools/inference-playground/src/main.rs`
- `tools/inference-playground/src/runtime/program.rs`
- `tools/inference-playground/src/runtime/machine.rs`
- `crates/yu-hir/src/module.rs` — support authenticated two-segment operation paths in selected source imports.
- `crates/yu-solver/src/candidate_source.rs` — inspect/fix exact Console candidate preflight only when needed.
- `crates/yu-solver/src/shadow_apply.rs` — preserve source-root context only when needed.
- this contract, `notes/theory/2026-10-22-r326-console-whole-module-runtime.md`, and `tasks/agent-loop/current.json`

Solver lease-entry hashes remain the revision-2 hashes recorded in revision 2. HIR module lease-entry hash is recorded in current state. No other paths are writable. No subagents, background work, fixture/expected-output rewrite, blanket staging, or history rewrite. R325's 1222 seconds are closed; R326 has a 2400-second cap and no carryover.

## Verification and boundary

Run exact Console through inference and runtime, focused host/whole-module tests, `cargo test -p yu-playground --lib`, `cargo check -p yu-playground`, sprint static check, sprint tooling tests, and `git diff --check`. Inspect the complete outbound range before any non-forced push. Do not claim R149 or a proof gate closed from these checks.

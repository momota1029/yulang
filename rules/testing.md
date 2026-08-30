# Testing and verification

## Start focused

Run the smallest check that directly exercises the changed responsibility, then broaden only when the focused result is understood.

For policy-only or repository-layout changes, the current deterministic baseline is:

```text
cargo fmt --check
cargo xtask check-graph
cargo check --workspace
```

These commands do not prove compiler behavior. Behavioral changes require relevant tests; broad checks do not replace focused tests.

## Verification budget

Follow the selected mode in `rules/orchestration-budget.md`.

- M0 record/comment/link changes: inspect the diff and run only checks needed for syntax or references. Do not run a workspace build merely because a progress file changed.
- M1 local gate: run focused tests/checks for the owning responsibility. A broad workspace check is normally deferred to the coherent phase boundary.
- M2 cross-layer/contract change: run focused checks plus one appropriate broad check after the repair round closes.
- M3 critical/final certification: run the full required gate once on the final candidate, not after every intermediate patch.

For a multi-gate Authoritative plan, focused checks run per gate; unchanged expensive workspace suites run once per coherent phase or final boundary unless the gate changes shared infrastructure that makes earlier broad evidence stale.

Do not rerun an unchanged expensive suite after bookkeeping-only, comment-only, or review-record-only changes.

## Test shape

Prefer:

- a small direct reproduction;
- the repository's existing fixture/golden form;
- a readable regression that names the contract;
- a sibling/generalized case derived from the root cause;
- explicit diagnostic text/span checks when those are contractual.

Avoid:

- giant tests with ambiguous failure causes;
- several independent spec changes in one case;
- tests that freeze incidental implementation detail;
- a new bespoke test format when an established one exists.

## Expected-output protection

Never update an expected value merely to match current implementation output. Expected values include:

- `assert_eq!` strings or structures;
- snapshots and golden files;
- expected types, effect rows, residuals, diagnostics, and spans;
- fixture metadata;
- a test name's semantic claim, such as `distinguishes` versus `coalesces`.

When a test fails, first assume the expectation may encode the intended contract. An expected-output update requires all of:

1. a reason, traced to the causal semantics, why the new behavior is correct;
2. confirmation that it matches an authoritative design/spec or an explicitly approved change;
3. a recorded explanation in the design, review record, or commit;
4. pre-write `spec_auditor` review once role orchestration is active.

Do not remove residual information, change a test's stated meaning, or weaken a diagnostic just to obtain green output.

## Heavy-suite safety

Do not run an unscoped or potentially heavy suite until its current resource behavior is known. If safety is uncertain:

1. inspect the current workspace and test inventory;
2. choose a module/test filter;
3. cap concurrency when appropriate;
4. establish monitoring or a kill condition for intentionally broad runs;
5. report what remains unverified.

The old yulang2 `infer` commands and skip patterns in `notes/incidents/yulang2-infer-test-memory.md` are forensic history, not commands for the current workspace.

Performance experiments and repeated timing runs follow `rules/performance.md`; test thoroughness alone does not authorize unbounded repetition.

## Completion evidence

Report exact commands and results. Do not treat a historical test count as a permanent expected count. A green build verifies only what it ran; explain omitted suites and remaining risk. Also report when a broad suite was deliberately deferred to the phase/final boundary.

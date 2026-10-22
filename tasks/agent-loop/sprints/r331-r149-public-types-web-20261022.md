# Sprint R331 — Simple-sub public types and R149 Web execution

Status: ACTIVE; primary-authorized solo continuation of the user's unchanged
Yulang2 playground goal. Dispatcher unavailable; no agents launched.
Branch / baseline: `research/simple-sub-intrusion`, `4efeb7617`.
Authority: R149 `notes/design/2026-10-20-r149-types-console.md`; inference
principles `notes/design/2026-10-11-yulang-inference-top-level-principles.md`;
legacy withdrawal `notes/design/2026-10-10-simple-sub-legacy-withdrawal.md`.

## Original outcome and success evidence

The parent remains: unchanged Yulang2 playground samples work through ordinary
inference and execution, with source/native proof. R149's exact Types and
Console bytes remain pinned and unmodified; no spelling-specific intrinsic,
prefix extraction or injected `main` is allowed.

This increment makes the Simple-sub candidate result capable of supplying
accepted public type observations and connects the same result to whole-module
WASM execution and the browser. Types must show polymorphic `id`, `answer: int`,
`name: str`, `pair: (int, str)` and capture `(42, Yulang)\n`. Console must
capture `hello from Yulang\n` then `3\n`. Inference, public types and output
publish atomically from one accepted result. The browser smoke must build a fresh
WASM artifact and run both exact pinned templates.

Current counterevidence: `CandidateSolvedResult` has no closed types or schemes;
`finish_candidate` asserts that absence. The browser only includes older sample
fixtures, while its WASM exports graph inspection and selected-definition run.
No R149 public type or Web execution evidence exists yet.

## Proof and implementation stages

1. Derive a Simple-sub public projection from retained candidate rows, levels,
   bounds, generalization boundaries and same-use FreshUse. Do not call the
   legacy F5/closed-scheme path. Show that the projection preserves accepted
   source observations and withholds output on conflicts/resource exhaustion.
2. Connect the exact `LocalSource` roots and selected FieldTail member evidence
   to the same projected Types result and the typed application rule. Existing
   source-to-constraint/runtime identity lemmas are conditional inputs; prove
   their missing model, source typing and consumer premises or retain them open.
3. Export public Types and whole-module captured output from the inference
   playground and WASM. Update the Web selector, Types display and smoke test
   to use unmodified R149 sources and the same accepted inference result.
4. Run focused solver/playground tests, `cargo test -p yu-playground`, and the
   fresh WASM/Web check. Record output order, inferred types, all-source coverage,
   failed publication behavior, and any precise remaining proof premise.

Success is the actual R149 Web smoke plus an accepted type projection whose
source/solver correspondence is established for the exercised constructors.
Tests alone do not close source adequacy, general soundness, principality,
termination, all Y2 samples, independent review or production admission.

## Exact primary leases

- `crates/yu-solver/src/lib.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `tools/inference-playground/src/lib.rs`
- `tools/inference-playground/tests/cli.rs`
- `apps/yulang-wasm/src/lib.rs`
- `web/playground/src/main.ts`
- `web/playground/index.html`
- `web/playground/src/style.css`
- `web/playground/smoke-test.mjs`
- `notes/theory/2026-10-22-r330-console-role-frontier.md`
- this contract
- `tasks/agent-loop/current.json`

No other writer or reviewer is active. No semantic change, old-solver bypass,
special-case name rule, scope reduction, F5 dependency, or production promotion
is authorized. A missing proof premise blocks only dependent publication; keep
independent source/runtime work moving.

## Resources, review and continuation

Primary-only serial work, 2400 active seconds, no carryover. At most one heavy
Cargo/build/test process; run focused evidence before the package suite. Current
review status is UNREVIEWED and solo; no self-review claim. Freeze direct source,
solver and test artifacts for a fresh independent review when a reviewer is
available. Only the primary stages explicit paths and pushes non-forced.

Continue related derivation and implementation stages under these leases. At a
material blocker, counterexample, integration seam, lease change or sprint end,
consult the dispatcher if available; otherwise record solo degraded dispatch.
STOP or session end cannot leave a writer RUNNING without a current receipt.

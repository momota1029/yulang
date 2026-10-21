# R254 — propagate ordered Tuple comparisons through the live solver

Status: RESULT_PARTIAL; Luna primary working solo. No delegated workers or active external writers.
Branch / baseline: `research/simple-sub-intrusion` / current R253 worktree atop `5596b1598`.
Authority: R149 unchanged sample semantics; R168 §§3–6, especially M6–M8; R253 native term result (unreviewed prerequisite).
Contract revision: 1. Resource envelope: 1200 seconds, no carryover.

## Original outcome and success evidence

The unchanged Yulang2 Types and Console samples must infer, display, and execute according to R149. Continue the Types critical path by making equal-arity Tuple bounds emit every same-index value constraint through the live worklist, with honest mismatch diagnostics for unequal arity and Tuple/other shapes. This remains a native solver step, not sample support.

Required falsifiers: unequal arity must emit no child constraints; equal arity must emit all positions, including repeated equal handles; reversed or heterogeneous positions must not be sorted or dropped; nested tuples remain nested. Rollback, diagnostics, candidate context and retained resources must preserve child index and admission ownership.

## Open premises and boundaries

R253 native Tuple storage and this live step are unreviewed. The full solver suite did not finish in R253; its default run stack-overflowed and serial run exposed an unresolved normalization test failure before cap. The same full suite was not rerun here; neither failure is attributed to Tuple.

Source candidate generation, extrusion/capture/freshening, candidate schemes, closed public types, ordered runtime evaluation, Console colon-application/import path, source/native proof, independent review and original sample behavior stay OPEN. No sample or expected-output edits.

## Exact writes and checks

Writes: `crates/yu-solver/src/term.rs`, `crates/yu-solver/src/lib.rs`, `crates/yu-solver/src/candidate_context.rs`, `crates/yu-solver/src/shadow_apply.rs`, `crates/yu-solver/src/candidate_scheme.rs` (test exhaustiveness only), `crates/yu-solver/src/candidate_context_tests.rs`, `crates/yu-solver/src/candidate_unit_tests.rs`, `crates/yu-solver/src/tests/kind_qualified_graph.rs`, `tasks/agent-loop/current.json`, this contract, and `notes/theory/2026-10-21-r254-live-tuple-comparison.md`.

R254 result: native equal-arity live Tuple propagation is implemented. Each source position gets a child value task and diagnostic edge; candidate routes use a dedicated Tuple continuation and `TuplePort { index }`, with transaction rollback restoring the saved frame/worklist/dependencies. Arity mismatch and Tuple/other mismatch are caught before child admission. Candidate source dependency observations retain the Tuple index. The diagnostic witness carries the first tuple index; FIFO bucket capacity now accounts for its added path rank.

Focused evidence: `cargo check -p yu-solver --features shadow-apply-candidate` passed. `cargo test -p yu-solver --features shadow-apply-candidate --lib tuple` passed 3 tests: native Tuple storage, equal-arity comparison/diagnostics, and candidate indexed continuation with rollback/resume. The `f5c_normalization::tests::transferred_member_outputs_have_a_simultaneous_index_peak` failure reproduces with `IdentityExhausted` both in this worktree and in a detached baseline worktree at `5596b1598`, so it predates R253. `python3 tools/agent_sprint.py check` and `git diff --check` passed. `cargo fmt --check` reports repository-wide pre-existing formatter drift, so no mass formatting was applied. The full solver suite remains unverified.

R149, R168 proof closure, source candidate construction, extrusion/capture/scheme transport, closed public types, runtime and original sample support remain OPEN. The current result is provisional native implementation evidence only.

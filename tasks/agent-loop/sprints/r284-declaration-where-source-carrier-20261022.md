# R284 — Preserve declaration prerequisites through source preflight

Status: CHECKPOINTED_UNREVIEWED; primary-authored solo under user direction.
Branch: research/simple-sub-intrusion. Baseline: R283 `7f823c475`.
Authority: ongoing user goal to run unchanged Yulang2 Types/Console samples under ordinary tests; this slice records declaration `where` clauses without resolving role identity or promoting semantics. R283 remains read-only and unchanged.

## Outcome

The source carrier now retains ordered declaration `where` clauses by source key, byte range, and exact text. Its block walker accepts only the retained leading preamble and never turns clauses into expressions. Candidate preflight rejects carriers with prerequisites because no identity-bound constraint consumer is implemented yet. This prevents silently dropping constraints.

Tuple additions in closed scheme views are handled explicitly by the test-only F5c decoder (unsupported), transport exporter (unsupported), and canonical probe token stream (distinct ordered tuple tags). No tuple is recast as union/intersection.

The ordinary solver example build exposed stale assumptions in two examples: `research_accepted_call_vertical` now iterates the `LocalSource::expressions()` slice explicitly; `research_scoped_formal_replay` imports `ComponentKind` from `yu_types`, debugs optional fresh endpoints, and passes its row identity by value. These compatibility fixes restore compilation without changing either example's assertions.

## Evidence and limits

Passed: `cargo test -p yu-hir --features shadow declaration_where_preamble_is_retained_without_becoming_an_expression -- --nocapture`; `cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_preflight_does_not_drop_retained_declaration_prerequisites -- --nocapture`; `cargo test -p yu-solver --features shadow-apply-candidate --no-run`; `python3 tools/agent_sprint.py check`; `python3 -m unittest discover -s tools -p 'test_agent_sprint.py'`; `git diff --check`.

The first one-clause solver fixture exposed a HIR walker bug: it toggled the body statement/separator state after a `WhereClause`, though that preamble node is not part of the alternating body sequence. The walker now leaves that state unchanged; the focused solver test covers one clause, and the HIR test covers repeated clauses. Existing package warnings remain. No independent review, role-name resolution, constraint generation, sample execution, theorem closure, or production promotion is claimed. Next: map retained prerequisite type/role names to exact identities, generate constraints, and follow them through propagation and runtime for the unchanged samples. Preserve the correction that contravariant `[io]` means `[io,'e]`; a `[state]` callback is not rejected solely for differing from `[io]`.

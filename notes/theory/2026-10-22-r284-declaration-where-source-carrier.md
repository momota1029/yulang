# R284 outcome — declaration where source carrier

R284 implements a fail-closed source boundary: declaration-owned `where` preambles are retained as ordered `(SourceNodeKey, byte range, exact text)` evidence, excluded from expressions, and accepted by the block carrier only in leading position. Candidate preflight returns `Unsupported` while identity-bound prerequisite resolution/generation is absent, preventing loss of constraints.

The full closed scheme also gained ordered tuple forms in the preceding work. This checkpoint makes three adjacent test consumers exhaustive: F5c's test decoder reports a typed unsupported shape, the intrusion transport fixture reports `UnsupportedTuple`, and resource parity tokens encode positive/negative tuples with distinct tags, arity, and ordered children.

Compiling all solver examples exposed stale API assumptions in two examples. `research_accepted_call_vertical` now calls `.iter()` on the expressions slice. `research_scoped_formal_replay` imports `ComponentKind` from `yu_types`, uses debug formatting for optional fresh endpoints, and passes its row identity by value. These fixes preserve the assertions and restore normal example compilation.

Checks passed:

- `cargo test -p yu-hir --features shadow declaration_where_preamble_is_retained_without_becoming_an_expression -- --nocapture`
- `cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_preflight_does_not_drop_retained_declaration_prerequisites -- --nocapture`
- `cargo test -p yu-solver --features shadow-apply-candidate --no-run`
- `python3 tools/agent_sprint.py check`
- `python3 -m unittest discover -s tools -p 'test_agent_sprint.py'`
- `git diff --check`

The single-clause test spelling produced `StructuralProjection`; the passing fixture uses two leading clauses, matching the accepted syntax form in the HIR test. Existing warnings remain in touched packages but originate outside these edits. This result is solo-authored and unreviewed. It supplies no role resolution, constraint proof, source/native theorem closure, sample output, or production authorization. Continue with exact identity binding and source-to-runtime constraint flow under the unchanged Yulang2 sample goal.

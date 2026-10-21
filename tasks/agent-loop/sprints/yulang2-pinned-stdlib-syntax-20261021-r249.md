# R249 — package the pinned standard library and use its imported syntax

Status: ACTIVE; solo primary implementation and source correspondence.
Baseline: `b0c3c853c`; parent goal remains the unchanged Yulang2 playground
sample behavior with implementation and proof completed.
Resource envelope: 900 seconds, no carryover; no subagents per user direction.

## Outcome

Make the authentic 40-file R149 standard-library closure available from files
inside this repository, keyed by the exact blob IDs in R149 rev10. Add a small
path-based loader for those pinned source bytes and use the actual
`std::core::ops` source header to create the playground parser's imported
operator environment. This must remove syntax recovery for the unchanged
Console template's `+` application without fabricating an operator by name.
An ordinary focused regression must verify every bundled source against its
Git blob ID and verify `+` provenance points to `lib/std/core/ops.yu`.

The source list and expected IDs are the complete closure in
`tasks/agent-loop/sprints/yulang2-types-console-20261020-r149-rev10.md`.
All 39 objects are present in this repository's Git object database. The
bundle is source data, not a generated substitute: each record retains its
relative path, original Git blob ID and exact bytes.

## Exact write paths

- `tools/inference-playground/pinned_stdlib.bin`
- `tools/inference-playground/src/pinned_stdlib.rs`
- `tools/inference-playground/src/lib.rs`
- `crates/yu-syntax/src/syntax_environment.rs`
- `crates/yu-syntax/src/full_parse.rs`
- `tasks/agent-loop/sprints/yulang2-pinned-stdlib-syntax-20261021-r249.md`
- `notes/theory/2026-10-21-r249-pinned-stdlib-syntax.md`
- `notes/progress/2026-10-21-r236-r246-history-archive.md`
- `tasks/agent-loop/current.json`

No HIR name/semantic import resolution, tuple lowering, role selection,
runtime, output, Web/WASM, expected-output or proof-gate edits are in this
increment. Do not claim the source loader or syntax import accepts either
sample semantically.

## Checks and falsifiers

Run focused `yu-playground` tests for the pinned bundle and imported `+`, then
run the exact unchanged Console template through the CLI and record its next
failure. Run `rustfmt --check` for edited Rust and `git diff --check`.

Falsifiers: any bundled byte fails its pinned Git blob ID; module path lookup
returns another source; the parser operator lacks Imported origin or the exact
dependency path; the unchanged `+` expression still produces syntax recovery;
or the CLI begins accepting a library name through spelling-only behavior.
The R149 semantic, tuple, role, execution, output and proof obligations remain
OPEN.

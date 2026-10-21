# R248 — imported operator headers into the syntax environment

Status: ACTIVE; solo Luna implementation and source correspondence. No subagents.
Baseline: `706970373` (`research/simple-sub-intrusion`). Parent goal remains the unchanged R149 Yulang2 playground sample behavior plus broader compatibility and proof.

## Outcome

Provide a source-keyed path from an imported dependency's scanned operator header facts into `SyntaxEnvironment`, preserving dependency slot, source range, and provenance. Use the exact R149 `core/ops.yu` `infix (+)` declaration as the discriminating regression: with that imported syntax fact, unchanged `say: 1 + 2` must parse without syntax recovery. The parser must continue to reject duplicate imported fixity conflicts and missing dependency provenance. This is a syntax integration increment, not standard-library loading, semantic import resolution, sample acceptance, or sample completion.

R149 design is authoritative at `notes/design/2026-10-20-r149-types-console.md` (SHA-256 `1644743185363d3c258c606a2e65245b3db8206dddeb666d2994e2471d74f7fa`). Its source evidence records `core/ops.yu:29` as `pub infix (+) 5.0.0 5.0.1 = \\x -> \\y -> x.add y` and the authentic dependency as blob `575e6fb15ce2d91a39004bbc7b842fedb2d83fdf`. The Y3 CLI currently passes `SyntaxEnvironment::empty()` in `tools/inference-playground/src/lib.rs::prepare`; no resolver supplies the authenticated imported header yet.

## Exact write paths

- `crates/yu-syntax/src/syntax_environment.rs`
- `crates/yu-syntax/src/operator_compilation.rs`
- `crates/yu-syntax/src/operator_table.rs`
- this contract, `notes/theory/2026-10-21-r248-imported-operator-environment.md`, and Luna-owned `tasks/agent-loop/current.json`

No playground, HIR, solver, runtime, fixture, or expected-output edits in this packet. The generic constructor is not to fabricate library declarations; it accepts already scanned imported `HeaderInfo` plus matching provenance.

## Checks and boundary

Run focused `yu-syntax` tests for imported-header construction, conflicts, provenance, and parsing `say: 1 + 2` with the R149 declaration supplied through the imported environment. Run `cargo fmt --check` for edited Rust. Do not run a broad workspace suite. Record exact output and update the inaccurate R247 Console diagnosis: the error span `88..91` in the exact 92-byte source is `+ 2`, not `say`; `say: 1` alone and `say: 1 + 2` with the local operator header both parse without syntax diagnostics. The absent imported operator table is the first parser seam.

Falsifiers: imported declaration becomes Local; source range or dependency slot changes; missing provenance or duplicate same-fixity import is accepted; exact operator application still creates syntax recovery; ordinary local declaration precedence changes. No proof or sample claim follows from syntax parsing alone. Keep the complete R149 source resolver, imported semantic environment, tuple and role/type implementation, whole-module execution, host writes, public type output, A/B/R70/R71/R72, soundness, principality, and production OPEN.

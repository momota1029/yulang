# R247 — Yulang2 playground sample baseline

Status: RESULT; read-only baseline and first-failure localization. Parent goal remains active.
Baseline commit: `b209e0828` on `research/simple-sub-intrusion`.

## Fixed outcome

Keep the user's unchanged goal: make Yulang2 playground sample programs run in ordinary tests, with the required implementation and proof completed in this repository. Establish which checked-in playground examples currently pass their ordinary CLI regression tests, then run the exact R149 Types and Console templates unchanged through the current CLI and record the first observed failure for each. This is evidence about the current boundary, not a reduced compatibility goal.

## Authority and pins

- Authoritative exact Types/Console behavior: `notes/design/2026-10-20-r149-types-console.md`, SHA-256 `1644743185363d3c258c606a2e65245b3db8206dddeb666d2994e2471d74f7fa`.
- Tuple constructor/consumer matrix and unresolved source seams: `notes/theory/2026-10-20-r168-ordered-tuple-construction.md`, SHA-256 `c88ce484dd1a6456f4e29cfcd932438db9ef6579f30584bc826aab9e4975a886`.
- Current source owners inspected: `crates/yu-hir/src/module/local_source.rs` `7d45e98690551f81f7b18e1778a934c65c43c8e17ed06bff110877b86bf5f14a`; `crates/yu-syntax/src/expression/tails/colon.rs` `df37d747f396e8b27c53b6785e4a26f5210162b14e65b4648d449495bf8f5982`; `crates/yu-syntax/src/root_statement.rs` `c6d1dc49625d1687ff0dae8f6808f4c97c3f78398aae3bc061c44b6fc9661626`.

## Exact checks and result

The existing checked-in `web/playground/examples/` contains six `.yu` files: identity island, ordinary islands, type mismatch, parameter provenance, repeated choice, and polymorphic escaping closure. Their current ordinary CLI test coverage passed in two focused Cargo invocations:

```text
cargo test -p yu-playground --test cli_yulang2_diagnostic_examples --test cli_demo_identity --test cli_ordinary_islands -- --nocapture
  1 identity test + 6 ordinary-island tests + 1 diagnostics test: PASS
cargo test -p yu-playground --test cli_repeated_choice --test cli_polymorphic_escaping_closure
  1 repeated-choice test + 1 polymorphic-closure test: PASS
```

The six checked-in source files therefore have existing passing CLI coverage; this does not establish R149 Types/Console compatibility or Web/WASM behavior.

The unchanged 142-byte Types template from R149 was piped to `cargo run -q -p yu-playground -- -`. It exited 1 with `candidate lowering unavailable: StructuralProjection`; the current HIR `LocalSourceForm` explicitly refuses comma-delimited `ParenthesizedExpression`, including `(answer, name)`. The unchanged 92-byte Console template was run the same way. It exited 1 with a structural `ErrorGroup` on `say: 1 + 2`; `colon_tail_normalized` declines colon tails in `MlMode::None`, so the root expression parser leaves the colon form as an error. Neither run reaches standard-library resolution, host writes, whole-module execution, or the required public Types result.

No source edits, test edits, expected-output changes, builds beyond those performed by `cargo test`/`cargo run`, or Web/WASM checks were made. Existing compiler warnings appeared during Cargo runs; all focused tests passed. Exact samples remain unsupported and the parent goal is not complete.

## Next action

Continue with the unchanged R149 target, not a redefinition around the six already passing fixtures. The first failure seams are comma-tuple source formation/type/runtime support for Types and root colon-application syntax for Console. The full R149 dependency chain still includes public tuple types, authentic library/source resolution, ordered whole-module execution, identity-bound `out::write` handling, atomic publication, and source/native proof. Use a new exact implementation contract before changing those owners; preserve the existing output and sample bytes. Parent A/B, R70/R71/R72, soundness, principality, and production gates remain OPEN.

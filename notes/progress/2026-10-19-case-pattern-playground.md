# Experimental case pattern path

## Result

The existing `case` syntax now reaches the experimental LocalSource inference
carrier and provisional playground evaluator for integer literal patterns,
arm-local identifier binders, and `_`. The evaluator checks arms in source
order. A binder receives the original scrutinee value and is visible only in
its arm body. The browser playground includes integer-match and binder
examples; the binder smoke uses one function at both integer and string types.

This is a guessed, bounded source slice. It does not define complete case
semantics or change the production compiler path. Guards, labels, structured
patterns, and static exhaustiveness remain unsupported here. The evaluator
reports a runtime limitation when no arm matches.

## Evidence

- `cargo check -p yu-solver`: PASS.
- `cargo check -p yu-playground`: PASS.
- `npm run typecheck` in `web/playground`: PASS.
- `npm run check` in `web/playground`: PASS; inference and 10 execution examples,
  including integer, wildcard and binder case branches.
- A paired CLI negative with the binder referenced after its `case` fails
  closed as unsupported; it does not produce a runtime value.
- `git diff --check`: PASS.

`cargo fmt --all -- --check` reports formatting differences across many
pre-existing files; no workspace-wide formatting was applied.

## Remaining boundary

This is executable evidence for the experimental source/evaluator route only.
It is not a proof, independent review, Yulang2 compatibility result, semantic
adoption, or production admission. Original Simple-sub/evaluator A/B, R85
adoption, R119 M/T/A, and the effect-hygiene parent gates remain OPEN.

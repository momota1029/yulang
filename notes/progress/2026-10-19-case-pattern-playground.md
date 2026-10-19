# Experimental integer case path

## Result

The existing `case` syntax now reaches the experimental LocalSource inference
carrier and provisional playground evaluator for integer literal patterns and
`_`. The evaluator checks arms in source order. The browser playground adds an
integer match example; the WASM smoke covers both the integer arm and wildcard
fallback.

This is a guessed, bounded source slice. It does not define complete case
semantics or change the production compiler path. Pattern binders, guards,
labels, other pattern forms, and static exhaustiveness remain unsupported here.
The evaluator reports a runtime limitation when no arm matches.

## Evidence

- `cargo check -p yu-solver`: PASS.
- `cargo check -p yu-playground`: PASS.
- `npm run typecheck` in `web/playground`: PASS.
- `npm run check` in `web/playground`: PASS; inference and 9 execution examples,
  including integer and wildcard case branches.
- `git diff --check`: PASS.

`cargo fmt --all -- --check` reports formatting differences across many
pre-existing files; no workspace-wide formatting was applied.

## Remaining boundary

This is executable evidence for the experimental source/evaluator route only.
It is not a proof, independent review, Yulang2 compatibility result, semantic
adoption, or production admission. Original Simple-sub/evaluator A/B, R85
adoption, R119 M/T/A, and the effect-hygiene parent gates remain OPEN.

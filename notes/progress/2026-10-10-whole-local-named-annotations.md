# Whole-local named annotations (2026-10-10)

## Result

The live candidate path now admits named type variables recursively in whole-
local value annotations over `Int`, `Unit`, `Variable`, and pure `Function`
trees. The annotation pair shares its named variables with the local binding's
formal annotations, while each distinct `HirLocalId` gets an isolated scope.
Each use still freshens the installed local scheme. The whole synthesized
initializer is checked against the negative interface and the positive
annotation interface is exposed at the child level. Initializer effects remain
one-shot; local lookups remain pure. Explicit effect rows, including `[]`, and
unfinished formal forms remain unsupported.

## Review and verification

Pre-write spec review confirmed this local extension fits the existing
annotation gate, provided variable scope follows actual local identity. A
post-write compiler review found no blocking or major semantic issue. It asked
for stronger effect-flow test evidence; the test was repaired to inspect the
enclosing result's Effect component, and primary inspection plus focused checks
closed that minor finding.

- `cargo test -p yu-solver --features shadow-apply-candidate --test candidate_annotated_primitive_formals --offline -j 2 -- --test-threads=1` — 19 passed.
- `cargo test -p yu-solver --lib local_annotation --features shadow-apply-candidate --offline -j 2 -- --test-threads=1` — 1 passed.
- `cargo test -p yu-solver --lib annotated_local_initializer_effect_has_one_block_edge_and_pure_lookups --features shadow-apply-candidate --offline -j 2 -- --test-threads=1` — 1 passed.
- Earlier on the same implementation, `cargo check -p yu-solver --all-targets --all-features --offline -j 2`, the formal-annotation integration target (6 passed), and the annotated-function-formals target (10 passed) passed. The later delta changed only tests.
- `git diff --check` — passed.

No benchmark or timing sample ran. Whole-local concrete effect rows and
effect-hygiene semantics, complete Call, public/default routing, soundness and
principality, and F5 replacement remain open. This slice does not establish
the separate `run_io` result example.

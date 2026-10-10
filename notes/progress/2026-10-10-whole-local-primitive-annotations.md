# Whole-local primitive value annotations (2026-10-10)

## Result

The live candidate source path now retains and consumes whole-local `Int` and
`Unit` value annotations. The initializer's synthesized value is checked
against the annotation's negative interface; the annotation's distinct
positive interface becomes the live local root at the initializer child level,
with the enclosing boundary retained for ordinary use-time freshening.
Initializer evaluation effects remain on the existing one-shot block edge,
and local reads remain pure. Other whole-local annotation forms remain
explicitly unavailable in this slice.

The shared local scheme installer now journals each slot it publishes during a
route transaction. Rollback clears only those newly published slots before
restoring candidate state; pre-existing local schemes remain intact. Tests
cover failure after fresh-root publication, publication from an existing
parameter root, preservation of a prior slot, and successful retry.

## Verification

- `RUSTC_WRAPPER= cargo test -p yu-hir annotated_primitive_formals --offline -j 2` — 2 passed.
- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --test candidate_annotated_primitive_formals --offline -j 2` — 11 passed.
- `RUSTC_WRAPPER= cargo test -p yu-solver local_annotation --features shadow-apply-candidate --offline -j 2` — focused rollback and annotation cases passed.
- `RUSTC_WRAPPER= cargo test -p yu-solver local_scheme_publication_rollback_preserves_prior_slots_and_retries --features shadow-apply-candidate --offline -j 2` — 1 passed.
- `RUSTC_WRAPPER= cargo check -p yu-solver --features shadow-apply-candidate --offline -j 2` — passed.
- `git diff --check` — passed.

The compiler-referee review found a rollback hole in local scheme publication.
The repair journals published slots directly, accounts for journal capacity in
all resource formulas, and adds the existing-root and prior-slot regression.
The independent delta review closed with no finding. No broad workspace suite
or performance measurement ran. The residual-owner question
remains open and blocks contextual residual/formal-row integration; Call,
effect hygiene, public/default inference, and F5 cutover remain open gates.

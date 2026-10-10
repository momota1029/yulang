# Whole-local ground Function annotations (2026-10-10)

## Result

The private candidate path now accepts whole-local annotation trees composed
only of `Int`, `Unit` and pure `Function` nodes. It rejects a type variable or
an explicit effect row at any depth, including explicit empty rows. The source
initializer is checked against the paired negative annotation built with the
definition's shared `SignatureContext::Annotation`; a distinct positive root
is published at the initializer child level using the enclosing generalization
boundary. Existing composed polarity and omitted effect-port behavior are
reused unchanged.

Initialization remains a one-shot block effect edge, while local reads remain
pure. The implementation uses the existing local slot journal and accounts
constructor-map scratch through success and failure. The earlier local Function
literal fixture now constructs a candidate and reports a real whole-value
mismatch; variable/effect-row annotation and unfinished formal cases remain
explicitly refused.

## Review and verification

Pre-write spec review found the slice permitted by the existing concrete
annotation authority, with no new semantic decision. Post-write compiler review
found no BLOCKING, major or minor issue.

- `RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --test candidate_annotated_primitive_formals --offline -j 2` — 15 passed.
- `RUSTC_WRAPPER= cargo test -p yu-solver --lib local_annotation --features shadow-apply-candidate --offline -j 2` — passed.
- `RUSTC_WRAPPER= cargo test -p yu-solver --lib local_scheme_publication_rollback_preserves_prior_slots_and_retries --features shadow-apply-candidate --offline -j 2` — 1 passed.
- `RUSTC_WRAPPER= cargo check -p yu-solver --offline -j 2` — passed.
- `RUSTC_WRAPPER= cargo check -p yu-solver --all-targets --all-features --offline -j 2` — passed.
- `git diff --check` — passed.

No benchmark or timing sample ran. The work remains a private source-inference
slice: effectful/named-row whole-local annotations, complete Call, effect
hygiene, soundness/principality, public/default routing and F5 replacement
remain open.

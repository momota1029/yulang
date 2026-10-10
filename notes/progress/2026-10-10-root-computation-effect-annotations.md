# Root computation effect annotations (2026-10-10)

## Result

The private live candidate now checks an explicit root covariant effect row
against the actual initializer computation effect for whole-definition and
whole-local annotations. This closes the private candidate's former preflight
gap under the existing covariant `[E]` policy; it does not introduce a new
language rule.

The check uses the annotation's negative allowance with the same effect-variable
and view maps as value checking/exposure. The actual computation effect remains
on its existing one-shot evaluation edge. The allowance does not contribute an
effect, and local schemes still publish only their value interface. An omitted
root row preserves prior behavior. Closed listed rows accept matching concrete
effects; closed empty or unlisted rows reject them with annotation-position
provenance.

## Review and verification

Independent compiler review found no blocking, major or minor finding. It
checked both action owners, composed annotation context, allowance direction,
one-shot flow, absence of manufactured support, counters, provenance and
transactional rollback/retry. It did not certify root symbolic-tail/future-lower
correlation, Function-valued root initializers, complete Call, public/default
inference or full effect hygiene.

Focused checks:

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --test candidate_effect_annotation -- --test-threads=1` — 11 passed.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests::root_computation_annotation -- --test-threads=1` — 2 passed, including storage/scratch rollback and retry.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test -p yu-solver --features shadow-apply-candidate --test candidate_annotated_primitive_formals -- --test-threads=1` — 21 passed.
- Scoped `git diff --check` passed.

No broad suite or performance measurement ran. Contravariant concrete
subtraction, contextual residual identity, complete Call, full hygiene,
soundness/principality and public/default F5 cutover remain open. The pending
contextual residual-owner question continues to block only dependent work.

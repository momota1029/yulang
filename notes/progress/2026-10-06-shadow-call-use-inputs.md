# Shadow source call/use input join

Date: 2026-10-06
Baseline: `5c47db77e52a44bb69e7498c5282f53e57878e90`
Status: M1 shadow-only source-reference API; independently spec- and regression-reviewed
Claim class: syntax/identity plumbing, no semantic judgment
Authority: user-authorized shadow implementation lane; inferred Function call-view §§2–5

## Change

The default-off HIR shadow skeleton now exposes one lazy `SourceCallUseInput`
for each Apply whose direct callee is an already resolved Use. It reuses the
retained application, call-tail position, UseId, BinderId and whole argument
ExprId, and can iterate over retained parameter-annotation incidence records
for that exact binder. The `yu-core/shadow` facade re-exports the view.

This is only a reference join. A row does not assert that its binder is a
formal. An empty annotation iterator does not establish annotation absence or
that retained incidences are complete. It provides no ordinary Value typing,
role/entry, `F_cb`, `beta`/`Slots(beta)`, typed path, effect contribution,
receipt, owner/receiver, `U_c` interpretation or admission. All existing Apply
premises, including the applicability/interpretation stub, remain pending;
Q cannot discharge them. Grouped and computed callees remain in the general
Apply inventory but outside this direct-Use-specific iterator. Production HIR,
F5 and inference routing are untouched.

## Review and verification

- Pre-write `spec_auditor`: no concerns with the proposed structural projection.
- Post-write `spec_auditor`: no findings; exact ID joins, retained annotation
  limits, direct-callee exclusions and all five pending premises checked.
- Facade `regression_auditor`: no findings; the re-export follows the existing
  `yu-core/shadow` HIR-owned API pattern and remains behind the `shadow`
  feature with default features disabled.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow --lib shadow_call_use_source_inputs -- --test-threads=1` — 4 passed, 66 filtered.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-core --features shadow` — passed.
- `rustfmt --edition 2024 --config skip_children=true` on the four owned code
  files and `git diff --check` — passed.

The iterator traverses existing expressions once (O(E)); each row's annotation
query filters the retained incidence slice (O(A)). It creates no per-row
annotation vector or new heap collection. No broad suite, performance sample,
production inference check or language-output change was made. The four
structural tests cover the exact nested capture, repeated calls sharing a
binder but not occurrences, exact noninitial annotation IDs, grouped/computed
exclusion and preservation of pending premises.

The exact changed paths were `crates/yu-hir/src/shadow.rs`,
`crates/yu-hir/src/lib.rs`, the new focused test module, and
`crates/yu-core/src/shadow.rs`. The API change is reversible within the
opt-in shadow surface. Remaining limitation: annotation incidence coverage is
the previously retained projection only; formal applicability and semantic
interpretation remain open.

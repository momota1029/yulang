# Shadow retention for nested unary ordinary applications

Date: 2026-10-07
Status: implemented; M2 compiler-referee and regression reviews passed
Authority: user's default-off shadow/experimental implementation authorization
Baseline: `80b08a5b051e2a688d77bd62175725c950c3c747`
Implementation: structural identity plumbing only; no semantic or production inference authority

## Change

The shadow HIR builder now retains the existing declaration Lambda owner for an
exact unary `my` declaration when the already-supported ordinary projection is
a tree of `Use`, integer, `Group`, and `Apply` forms. The previous annotated
direct-body eligibility is preserved, and annotation-bearing nested bodies
remain excluded. The selected nested-block recognizer and its Lambda/Bind
projection remain separate.

The declaration is still appended after body projection. Existing body
expression IDs, parameter/use identities, CST positions, Apply topology and
ordered pending rows remain intact. The added repeated-use fixture
`my repeated f = f (f 1)` confirms both calls resolve structurally to one
parameter binder with distinct `UseId`s. The core inventory borrows the same
declaration owner for both registrations and rejects foreign artifact access.
Unary grouped/computed callee controls confirm only direct-Use calls register.

No role, type/effect, call-view, beta/profile, typed path, owner/receiver,
admission, contribution, licensing, solver, or inference judgment is added.
The production HIR and inference paths remain unchanged; the feature remains
default-off.

## Review and checks

- Compiler-referee review: PASS, no findings in the three-file implementation
  and original test delta.
- Regression-auditor review: PASS; its optional unary grouped/computed-callee
  coverage request was closed by a focused test and delta review.
- HIR focused tests: `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow shadow_source_core -- --test-threads=1` — 14 passed.
- Core raw inventory: `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-core --features shadow --test shadow_raw_structural_inventory -- --test-threads=1` — 9 passed.
- Feature-off package check: `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-hir -p yu-core` — passed.
- `rustfmt --edition 2024 --config skip_children=true --check` on the three changed Rust files — passed.
- `git diff --check` on the three changed Rust files — passed.
- Performance samples: zero; one linear borrowed-form scan in the opt-in shadow builder, no production hot path.

## Remaining boundary

This closes only a structural declaration-to-call identity seam. The call
contract and typed contribution remain unresolved premises. Soundness,
principality, source adequacy, source-wide applicability/admission, and
production inference cutover remain open.

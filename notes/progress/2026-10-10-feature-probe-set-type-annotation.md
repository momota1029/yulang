# Feature-probe test collection type

Date: 2026-10-10
Baseline: `bbdfd47f5`
Status: mechanical owning repair verified
Mode: M0; zero reviewers, zero measurement budget

An all-feature solver check during Unit integration exposed E0283 at
`src/tests/research_function_realization.rs:854`. The unchanged expected
`collect()` is ambiguous with the feature-probe `HashSet` equality adapter.
The same line and adapter exist in the inspected committed baseline; this
is not caused by the Unit changes.

Producer `legacy_collect_type_repair` adds only
`collect::<std::collections::HashSet<_>>()`. The existing left operand already
has that exact type; assertion values, fixture, test name and semantics are
unchanged. This cause is isolated in its own commit. No new design decision.

Primary checks on the final frozen combined worktree pass without warnings:

- `RUSTC_WRAPPER= timeout 180 cargo check -p yu-solver --all-targets --all-features -j 2 --offline`
- `RUSTC_WRAPPER= timeout 180 cargo test -p yu-solver --all-features --lib source_hir_function_realization_and_checked_lift_match_on_bounded_histories -j 2 --offline -- --test-threads=1`: 1 passed.
- Explicit one-line diff inspection and `git diff --check`: pass.

The combined worktree includes the independently reviewed Unit gate; this
record does not claim a separate historical-baseline build or broader proof.
No broad test suite, benchmark or expectation change was performed.

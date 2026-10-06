# Shadow formal-use applicability and interpretation stub

Date: 2026-10-06
Status: M1 shadow-only premise plumbing; independently spec-reviewed, no findings
Baseline: `b0dd026bb9438b7dfb13c68a474a49145eb97555`
Scope: HIR shadow artifact and focused shadow tests; production unchanged
Authority: explicit user authorization for unresolved shadow premises/stubs

## Change

Each retained Apply whose direct callee is an existing `Form::Use` now has an
additional pending `SourceFormalUseRuleApplicabilityAndInterpretation` premise.
It names a missing source-producer seam while keeping both applicability and
meaning unresolved. A resolved binder may be a declaration rather than a
formal; the artifact does not decide formal status, relevant-component scope,
annotation eligibility, ordinary-Value typing, or the whole original
`xi=(nu,K,D)` predicate. It derives no `Delta_formal` or `U_c`.

The four existing per-Apply premises remain unchanged. Integer, grouped and
computed callees receive no additional premise and remain covered only by the
general Apply inventory. The new stub does not select actual callable role or
entry, profile/typed paths, protection permissions, receipts, admission, or
`Q`; none can discharge it. No production HIR/F5/inference route changed.

## Review and verification

- `spec_auditor`: no BLOCKING, major, or minor findings. Confirmed unresolved
  applicability and interpretation, preservation of the original four
  premises, exclusion of non-Use callees, and no language-output changes.
- `RUSTC_WRAPPER= cargo test -p yu-hir --features shadow --lib shadow -j 2 -- --test-threads=1` — 42 passed, 24 filtered.
- `RUSTC_WRAPPER= cargo check -p yu-core --features shadow -j 2` — passed.
- `rustfmt --edition 2024 --check` on the five changed files and
  `git diff --check` — passed.

One Cargo process, at most two jobs, one test thread. No broad workspace suite,
production inference, performance sample, or Oracle execution. The structural
assertions count pending shadow records; no golden, diagnostic, fixture, or
language-semantic output expectation changed. Soundness, principality, P/A,
source adequacy, semantic discharge and production cutover remain open.

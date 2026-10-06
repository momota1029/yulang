# Shadow differential: frozen legacy Apply structure

Date: 2026-10-06
Status: M1 default-off shadow/test slice; spec-auditor reviewed; structural claim only
Yulang3 baseline: `8a51ce7f752b021c16c6ae4cbe83f5a32b0f3fc4`
Frozen reference: Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Authority: user's authorization for shadow/differential work; no Oracle semantic authority

## Result

Added a structural differential for the exact captured-step source
`my apply f = { my step x = f x; step }`. It compares the current shadow
skeleton against the independently recorded frozen poly expression dump after
normalizing only expression constructors and lexical identity edges:

```text
Lambda(f, Bind(step, Lambda(x, Apply(Use(f), Use(x))), Use(step)))
```

The strict legacy reader retains the frozen dump's expression, parameter,
definition and reference identities while checking uniqueness and resolving
every reference edge. It rejects unsupported or trailing input. Both sides
normalize to named binder roles, not allocation ordinals. The test checks four
distinct binders, seven distinct expression nodes, three distinct uses, the
exact ordered tree and use-to-binder edges, including the outer `apply` binder
that has no use. The source bytes retain the final line feed and match the
captured input SHA-256 `d05809782dce91cb83886e4d80da87a5a3a145d3518b1cfdec2da2d3ce64658c`.

This verifies shadow retention of ordinary Apply shape and lexical identities
against a separate recorded artifact. The frozen dump has no explicit capture
list: the inner `f` use demonstrates only a structural free-variable relation.
No scheme, typed capture, receipt, receiver, runtime, source-acceptance,
inference-parity, soundness, principality or source-adequacy result follows.
All existing pending call-view and event/output premises remain present and
unchanged. Production `ResolvedExpr` and F5 inference paths were not modified.

## Review and checks

- Pre-write spec-auditor review approved this exact structural-only contract.
- Post-write spec-auditor review found one major provenance issue: the source
  literal lacked the captured final LF. The primary added it and made the
  normalizer require the captured output's final LF; the recorded SHA-256 then
  matched. Delta review closed the finding with no residual issue.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow --lib shadow_legacy_apply_structure -- --test-threads=1` — passed (1 test; 79 filtered).
- `rustfmt --edition 2024 --check --config skip_children=true crates/yu-hir/src/tests/shadow_legacy_apply_structure.rs crates/yu-hir/src/lib.rs` — passed.
- Scoped `git diff --check` — passed.

One Cargo process ran with two build jobs and one test thread. No Oracle build,
execution or test was performed. Broad suites, production differential,
inference semantics, performance and all source/theorem proof gates remain
unverified or open.

# Effect intrusion fixtures: authentic source qualification

Date: 2026-10-16
Branch: `research/simple-sub-intrusion`
Baseline: `ab99531a3`; production inference unchanged
Status: three fixture repairs independently reviewed and verified
Mode: M1; pre-write spec audit and one semantic closure reviewer

## Cause and authorized repair

The three baseline failures recorded in `tasks/current.md` created extrusion
pairs without the source association required by the
[selected Value-reference SCC criterion](../design/2026-10-12-intrusion-value-type-association.md)
and [top-level principles §1.1](../design/2026-10-11-yulang-inference-top-level-principles.md).
Reciprocal Effect bounds do not qualify source intrusion. Existing sibling
fixtures in `candidate_intrusion_tests.rs` and `candidate_context_tests.rs`
already retain an authentic checking event around the actual extrusion.

The test-only helper in `crates/yu-solver/src/candidate_effect.rs` now selects
the real checking occurrence of a dedicated self-recursive `intrusion_seed`,
asserts sealed source qualification, and seeds its contextual Effect relation.
It installs that relation only while calling the actual extrusion and restores
the previous processing relation before returning either success or error.
The helper creates no Value edges and no alternate intrusion criterion.

Only these three source fixtures and their extrusion calls changed:

- `raw_and_canonical_effect_roots_replay_late_conflict_after_parent_copy_intrusion`
- `multiply_originated_bound_keeps_future_conflict_paths_through_extrusion_and_intrusion`
- `views_keep_fresh_use_ownership_and_intrusion_rollback_restores_relations`

Every original assertion, test name and reverse-bound operation remains.
The self-reference is internal/monomorphic; it adds no alias FreshRoute, so
the existing two-route assertion still holds. A stale timing comment is
corrected: qualifying extrusion queues equality, and the next typed drain may
settle it before the later explicit reverse bound. That bound is not the
source qualification event.

## Independent review and production preservation

Explorer `effect_fixture_source_owner` located the source cause and established
sibling pattern. Pre-write `spec_auditor` `ordinary_carrier_contract` cleared
the exact fixture scope, including preserving assertions and restoring context
on errors. `implementer` `ordinary_carrier_implement` produced the repair.
Independent `compiler_referee` `ordinary_carrier_semantic` returned CLEAN at
file SHA-256 `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9`.

Primary compared the entire prefix before `#[cfg(test)]\nmod tests {` against
`ab99531a3`: all 88,405 bytes are identical, SHA-256
`ca85b59afbdbbf33423196ae2a0dc5634a11a1d4220bdcb59af951ba7fc55979`.
The alternative prefix including that cfg attribute is 88,417 bytes, SHA-256
`78488c0728861348bf524b6494646c64bad41d7cfab28f3431f700df2667a776`.
No production constructor or consumer changed, so earlier production proof
reviews retain their scope despite the whole-file test delta.

## Exact verification

Primary alone ran these commands serially, each with a 180-second cap and
`CARGO_BUILD_JOBS=2`:

```text
cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests::raw_and_canonical_effect_roots_replay_late_conflict_after_parent_copy_intrusion -- --exact --nocapture
cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests::multiply_originated_bound_keeps_future_conflict_paths_through_extrusion_and_intrusion -- --exact --nocapture
cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests::views_keep_fresh_use_ownership_and_intrusion_rollback_restores_relations -- --exact --nocapture
cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests:: -- --test-threads=1
```

Each focused test passes. The bounded owning module reports **28 passed,
0 failed, 2 ignored**. The two existing ignored observations were not enabled.
No warnings or timeout occurred. Logs:
`/tmp/yulang-effect-fixture-{raw,origin,view,module}-20261016.log`.
`git diff --check` passes. No performance samples or measurement campaign.
The full solver/workspace suites were not repeated for this test-only repair.

This closes the three recorded fixture regressions. It does not prove global
intrusion eligibility, equality preservation, complete source/native adequacy
or F5 cutover. Current task and research queue record the repaired status.

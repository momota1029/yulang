# Context freshening checkpoint

Baseline: `59a15228c7b743d969c3823984a4a71bef18e661` on
`research/simple-sub-intrusion`.

## Gate and authority

This M2 implementation slice wires the approved contextual attachment design
§§3–5 into candidate scheme capture and per-use reconstruction. It preserves
the existing `post_check_context` policy, keeps equality/zero-use transport on
its existing path, and does not activate source operation execution or admit
negative concrete formal rows.

## Implementation

Captured bound fibers now retain every executable view payload referenced by
their post-check context DAG, including a context-only view's generic tail.
Freshening copies those views through the same `(view, mapped tail)` cache as
endpoint-reachable views, validates the old and copied view/weight ownership,
constructs explicit payload substitutions, and renames all bound roots with
one shared context map per use. The copied attachment bundles link to the
actual renamed child relation. Certificate-bearing `BothFromRight` contexts
remain unavailable because this branch has no authentic certificate owner.

Capture and use worklists/maps participate in their scratch ledgers. A fresh
rename records the simultaneous context-map, traversal, and rollback storage
peak. On failed capture/rename, context state is rolled back; a fresh map is
cleared while retaining its capacity charge so retry does not double-count the
allocation.

## Evidence

- Focused context tests: 53 passed.
- Focused effect tests: 27 passed.
- Candidate scheme filter: zero matching tests; no behavioral evidence.
- Scoped `git diff --check`: passed.
- Independent M2 compiler-referee and regression-auditor reviews: PASS. The
  compiler-referee's one minor finding on simultaneous map/traversal resource
  accounting was repaired and passed fresh delta review.
- Resource regression: a 130-node shared context DAG checks simultaneous
  capacity accounting, certificate-triggered rollback, supported retry, and
  release of retained map capacity.
- No benchmarks, broad checks, allocator-failure injection, or source Oracle
  execution. No timing samples or measurement processes were used.

## Remaining boundary

This closes only fresh-use capture/transport preparation for the currently
source-generated carrier. It does not prove complete contextual lifecycle
semantics, source operation execution, certificate ownership, soundness,
principality, Complete Call, or production/default/F5 cutover. Continue with
the exact two-cycle certificate invalidation, withdrawal, rollback, and retry
gate before recursively admitting nonempty contexts.

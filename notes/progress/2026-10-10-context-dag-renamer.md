# Detached context DAG renamer checkpoint

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Baseline: `32c65f076`
Authority: [contextual attachment admission design](../design/2026-10-10-contextual-attachment-admission-design.md), §§3–4
Mode: M1, one implementer repair round and one fresh compiler-referee delta review
Status: detached transport preparation only; no live lifecycle consumer

`State::rename_contexts` reconstructs a reachable context DAG from explicit
weight and opaque certificate-token substitutions. It preserves constructor
order, replay bracketing and shared children. Each per-use map retains one
construction per source node; distinct maps can produce distinct attachment
identities. Certificate substitution does not authorize an entry or discharge.

Caller-provided cache entries are validation candidates. The helper traverses
each reachable source DAG in postorder, checks every leaf substitution, and
compares any suggested target against the exact reconstructed constructor.
Malformed source/target handles and mismatched children return `Err` before
interning. On error, the helper removes only mappings it inserted, rolls back
new context nodes, and releases charged traversal/journal scratch. The caller
owns substitution/cache capacity and must invalidate the cache when an outer
route rolls back.

The initial compiler-referee review found a major cache-bypass defect: cached
roots could skip required substitutions, and a malformed cached child could
panic past rollback. The repair added cached-root and partial-child regressions.
A fresh compiler-referee delta review passed the frozen two-file repair,
including constructor validation, rollback and scratch restoration.

Focused check:

- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 cargo test --offline -q -p yu-solver --features shadow-apply-candidate --lib candidate_context::tests -- --test-threads=1` — 50 passed.
- `git diff --check` passed for the two implementation/test files.

No broad tests, allocator-failure injection, non-test build, live transport,
freshening, source operation execution, or timing measurements ran. Zero
measurement samples/processes. This helper does not close contextual lifecycle
transport, source attachment construction, recursive operation admission,
soundness/principality, or F5 cutover.

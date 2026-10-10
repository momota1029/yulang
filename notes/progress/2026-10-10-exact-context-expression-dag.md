# Exact contextual operation DAG foundation (2026-10-10)

Baseline: `f352d289e5c689629d1991caa85ef7d922c82bf6`
Claim class: private representation foundation; no production contextual propagation
Authority: `notes/design/2026-10-10-contextual-attachment-admission-design.md` §§3–4
Review: independent `spec_auditor`; no BLOCKING, major, or minor findings

The private candidate relation store now has an interned structural context DAG
for left-prefix weights, right-pop suffixes, Function `swap`, source-owned
`both_from_right`, ordered lower/upper replay, and left-filter erasure. Context
nodes preserve child identity, operation order, replay direction, and distinct
opaque weight/certificate handles. Invalid child handles are rejected as
internal invariant failures. Context nodes and interning keys participate in
route rollback and retained-capacity accounting.

The independent conformance review found that all production seed, admission,
bound, replay, and transport entrypoints still use the identity context. The
new nonidentity constructors are exercised only in unit tests, so this slice
does not admit relations with missing source payloads. The existing
same-endpoint/distinct-context test now constructs a valid interned context and
retains its prior expectation.

Verification:

```text
RUSTC_WRAPPER= timeout 180s cargo test --offline -p yu-solver --features shadow-f5,shadow-apply-candidate --lib candidate_context::tests -j 2 -- --test-threads=1
```

Passed: 12 tests, 0 failed. Also passed scoped Rust formatting and
`git diff --check`. No other test targets or performance measurements ran.

This closes only structural context identity. Authentic annotation/filter and
weight payload construction, the unresolved attachment-member grouping,
worklist/bound/replay propagation, freshening, residual recipes, two-circuit
acceleration and invalidation, full hygiene, complete Call, ordinary/default
publication, soundness/principality, and F5 retirement remain open. The
separate attachment-member identity question is recorded in the pending
question board and blocks only authentic construction whose cancellation
identity depends on that grouping.

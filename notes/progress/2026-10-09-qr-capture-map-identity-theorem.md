# Current Q/R capture-map identity theorem

Date: 2026-10-09
Baseline: `bed31069ac2e458ef4ff20a1e6084c1984af34a3`
Scope: bounded FRESH_LIFE sublemma for production-produced schemes; no successor or source-use correspondence

## Theorem

Fix one successfully returned immutable `SolvedModule`, a complete captured
incoming-use route, and its exact target scheme. The production Q/R inventory
maps totally and injectively to the captured row identities. Repeated
occurrences of one binder, both polarities, and recursive references share the
same substitution; distinct committed incoming uses have disjoint row images.
Capture preserves historical identity owned by that result, not a live solver
row capability.

The production-produced-scheme restriction is essential. `finalize_f5c_draft`
registers every Q before boxed finalization, and indexed validation requires
dense, disjoint R ordinals. The generic boxed finalizer alone only compares R
against registered Q entries: a synthetic header with `q=1`, `R ordinal=0`,
and no registered Q can pass that narrower validation and collide in the
ordinal-keyed substitution. This is not reachable through the inspected
production producer and is excluded from the theorem.

## Proof dependencies

- Fresh instantiation appends one row per binder to one substitution; positive
  and negative occurrences plus both restored R bounds read that substitution.
- A failed transaction truncates only its attempted suffix. Incomplete or
  failed captures do not publish, so later successful committed uses cannot
  alias a committed row.
- Capture completeness is checked against the validated inventory. Observer
  queries join the collection brand and exact target scheme; row identity also
  contains its capture owner.
- `SolvedModule` publishes captured identities and schemes after the solving
  session ends. It does not retain session bounds or establish successor
  reference validity, activation liveness, or expiry behavior.

Primary code locators: `crates/yu-solver/src/lib.rs` at 9114, 9716, 14422,
14549, 14758, 14923, 15535, and 15849; `crates/yu-solver/src/shadow_f5.rs`
at 287 and 328; `crates/yu-solver/src/shadow_scc.rs` at 53;
`crates/yu-types/src/lib.rs` at 428 and 3300.

## Independent review and limits

A compiler-referee review passed this production-bounded theorem and identified
the generic-finalizer counterexample above. The review did not establish
successor Q/R correspondence, liveness, split/merge/rebuild correctness,
dependency completeness, or atomic rebuild publication. FRESH_LIFE remains
open at those existing obligations. No Frozen Oracle semantics were used.

Checks: bounded source inspection and current-HEAD/origin equality. No tests,
builds, writes to compiler code, or Git mutations were performed for the proof.

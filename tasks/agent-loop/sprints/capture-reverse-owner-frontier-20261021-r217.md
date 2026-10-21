# R217 — Capture reverse-owner frontier

Status: ACTIVE, solo primary, candidate implementation and focused verification.
Baseline: `26fde472d`; branch `research/simple-sub-intrusion`.

## Objective

Make local candidate Capture discover an effect edge stored one-sided on the
lower row's `direct_upper_rows` when Capture first reaches the upper row. The
R187 Lambda slot-4 relation `Effect(10) <= Effect(31)` is the required witness.
This addresses candidate frontier traversal only; no native theorem or
production gate is closed.

## Exact paths and leases

Write only:

- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/shadow_apply/local_source_observation.rs`
- this contract, `tasks/agent-loop/current.json`, and one result note under
  `notes/theory/`

Baseline source SHA-256:

- `candidate_scheme.rs`: `a0d97d6d8d93bc8d1a7bc15b19c219b850ae4d2bfb4d00ed74d267c79ced3b11`
- `local_source_observation.rs`: `a90910095e5bfe17ede6e2df8da57149584cef97aea999a3da3dd14378b92487`

The reverse-owner lookup must be built at most once per Capture, and only for
effect rows reached from a nonmodule, positive-boundary captured type shape,
and only when the reverse edge has a completed direct Lambda slot-4 source
Origin. Module-level boundary-0 captures are unchanged, and bound-discovered
owners do not recursively widen the reverse frontier. Canonicalize both
endpoints, deduplicate aliases, use checked/reserved memory, and include the
index, origin set and shape-row set in Capture scratch accounting on success
and failure. Emit each
incoming relation through the existing `Capture::bound` path so evidence and
source-bound readback remain intact. Add a focused assertion that the same-use
relay Capture contains the exact source bound
`Effect(10), Negative, Effect(31)`, retains its lineage to relation 71, and
captures the owner row. Do not change
solver constraint admission, physical storage or production compiler behavior.

No subagents per the user's standing constraint. This solo implementation does
not claim independent review or authorize promotion of the original theorem.

## Verification

The focused source-route test passes after replacing brittle relation-ID
expectations with exact canonical bound keys. It confirms Effect(10) is in
Capture, the exact source bound is present under derived relation 72, and its
lineage reaches the Lambda slot-4 origin. The final edit also tightened
partial-index failure accounting.

`RUSTC_WRAPPER= cargo test -q -p yu-playground` passes all package tests,
including the ordinary Yulang2 playground sample coverage. The focused command
`RUSTC_WRAPPER= cargo test -q -p yu-solver --features
shadow-apply-candidate local_source_observation` passes its one matching test.

A full candidate-enabled `yu-solver` package run stopped before tests because
three unrelated research examples fail to compile against current APIs
(`research_accepted_call_vertical.rs` and `research_scoped_formal_replay.rs`).
The final sequential library run reached 77/732 tests, reported failures in
`captured_bundle_spans_are_sparse_and_shared_across_reconstruction`,
`operation_retirement_frontier_ignores_historical_capacity_and_untouched_pending_operations`,
and `parsed_literal_local_retains_nonempty_child_until_exact_once_receipt_delivery`,
then made no test progress while one process held a CPU continuously for over
90 seconds. I interrupted that run. These failures occur in `candidate_context`
tests; they are not established as baseline failures, and no full-library pass
is claimed. An earlier unrestricted reverse-closure attempt also expanded
unrelated effect-history components and pushed authentic-demand cases into
`IdentityExhausted`/stack overflow. The present lookup is restricted to
completed Lambda body-to-result origins on positive-boundary type-shape rows.

This closes only the bounded Capture-route implementation observation. The
original theorem, native correspondence, semantic approval and production
gates remain OPEN. Independent review was unavailable in this solo run.

An end-of-sprint dispatcher consultation was not launched because the user's
standing instruction forbids subagents. No next sprint or expanded lease is
created by this record.

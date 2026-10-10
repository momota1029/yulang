# Detached contextual numeric evaluator checkpoint

Status: reviewed M1 preparatory slice; source execution and the full contextual
lifecycle remain open
Baseline: `0fb0511ed`
Authority: `notes/design/2026-10-10-contextual-attachment-admission-design.md`
§§3–6; source-exact operation mapping in
`notes/progress/2026-10-10-contextual-effect-source-correspondence.md` §
“Exact contextual operations and four-port consumer” and
`notes/progress/2026-10-10-formal-filter-transition-contract.md`

## Change

The structural fold now has a detached numeric evaluator over explicitly
provided finite atom-set weights. It covers left prefix, right POP suffix,
swap, both-from-right, filter clearing, ordered replay, and directed mix. The
result retains the exact reachable `ContextId`/`ContextExpr` records, including
weight and certificate tokens, in addition to the evaluated value. Numeric
equality does not intern or rewrite construction records.

Counts use arbitrary-precision little-endian `u32` limbs with exact
compare/add/subtract and fallible reservation. This follows the approved
unbounded-context contract rather than copying legacy `u32` saturation. PUSH
families are finite resolved source-atom sets; `All` is a separate explicit
filter case. Attachment identity is separate from family equality. Same-ID
family mismatch returns the existing internal availability failure. The
evaluator remains detached from source payload construction, live worklist
execution, relation admission, certificate authorization, filter discharge,
residual/gamma construction, and `candidate_context_execute`.

The first implementation represented `All` in the same family enum used by
PUSH entries. Independent review found that this exceeded the approved finite
PUSH fragment. One batched repair split finite `DetachedPushFamily` from
`DetachedFilter::{All,Finite}` and corrected tests to reuse resolved source
identity. Fresh compiler-referee delta review passed.

## Review and verification

Selected mode: M1. Review convergence:

- Initial compiler-referee review: one major finding, the unsupported
  universal `All` PUSH family.
- One batched repair: separate finite PUSH families from filters and use
  consistent resolved identity in tests.
- Fresh compiler-referee delta review: PASS; prior operation/arithmetic review
  carried forward and the repaired domain boundary confirmed.

Focused verification passed:

- `RUSTC_WRAPPER= cargo test -q -p yu-solver --features shadow-apply-candidate --lib detached_ --offline --jobs=1 -- --test-threads=1` — 7 passed, 571 filtered.
- `git diff --check -- crates/yu-solver/src/candidate_context.rs crates/yu-solver/src/candidate_context_tests.rs` — passed.

No non-test build, broad suite, benchmark, or timing sample ran. Allocation
failure paths use fallible reservations and return the existing internal
availability error, but allocator fault injection was not available. No
performance measurement was needed for this detached helper; it has no source
execution call site. Any later connection to hot solver paths needs a fresh
cost and conformance review.

## Remaining gates

The following [source PUSH seed checkpoint](2026-10-10-context-source-push-seed.md)
now prepares one dormant unit-PUSH from admitted written covariant attachments
with nonempty resolved members. That seed is still outside live context
construction and execution.

This evaluator does not establish source-derived operation payload formation,
Function-port context propagation, relation-sensitive completion, attachment
freshening, executable filter ownership/discharge, residual/gamma consumers, or
the two-cycle certificate generation/invalidation/withdrawal/rollback/retry
gate. Recursive nonempty source contexts remain disconnected. General
mixed-component admission, complete Call, full effect hygiene,
soundness/principality, ordinary/default/public inference, and F5 retirement
remain open.

# R75 revision 2: exact source value identity projection

This revision preserves the R75 objective, source, C1 cut, total cap and all
parent statuses. It adds one test-only source lease in response to the first
exact missing premise recorded by frozen R75 proof revision 1.

## Frozen obstruction

R75 proof revision 1 is frozen at
`notes/theory/2026-10-19-r75-c1-identity-fidelity.md` (SHA-256
`5855746697852edfaff8311b1e6d0d9d47d9c81b30b04e56a1e6d472467615c0`) and
`tasks/agent-loop/inbox/20261019-r75-proof.md` (SHA-256
`35c1319f5dfb4fb7fc50a6c953eea9c7fc1658b2b4897d1afdb628b99788a627`). The
author is STOPPED. Its authentic-equality and conditional provenance/erasure
lemmas remain usable only conditionally; exhaustive coverage remains OPEN.

The fixed source plan retains `candidate_value_graph::Graph`. Its private
`modules`, `vertices`, and `values_by_ordinal` maps and `checking_by_event`
vector cannot be exhaustively observed through point queries. `checking` is
already public, so it is not a missing API. Preserve the obstruction artifacts
and do not restart that proof author.

## Exact lease addition

Add Luna write ownership of
`crates/yu-solver/src/candidate_value_graph.rs`, whose pre-revision-2 SHA-256 is
`8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50`.
Permit only `#[cfg(test)]` immutable projections that enumerate the actual
`modules`, `vertices`, and `values_by_ordinal` map entries, plus actual
`checking` entries and indexed `checking_by_event` contents. Preserve typed
keys/values, vector indices, and multiplicity. Do not derive one container
from another: disagreement between redundant indexes must remain visible. No
mutation, canonicalization, solver ordering/control change, Debug-based
identity recovery, production path or semantics change.

The existing test-only read accessors in `candidate_source::Plan.references`
remain pinned. Document whether the relevant identity relationship is the
actual projection of that owner; do not claim a complete inventory from
point-query samples. Stop if another unleased field is required for the exact
R75 completeness claim.

## Resources and status

No budget increase or reset. The total cap remains 2400 seconds, reserved as
Luna 900 (includes exactly one focused command of at most 180 seconds), Sol
proof 600, fresh compiler 300, fresh spec 300, and Luna integration 300; Astra
0. R75 proof revision 1 remains STOPPED with its 600-second reservation charged
and unknown elapsed. No work or remaining-time claim is inferred from that
reservation. The single focused command has not been used. Luna may implement
the accessor within the original implementation envelope; if completion does
not fit the remaining envelope, stop OPEN without a retry or an implicit grant.

The existing identity ledger, owner dictionary, fidelity requirements,
review seam, output paths, and all other authority in revision 1 are unchanged.
Fresh reviewers must see this revision, the stopped proof obstruction, and the
final single frozen snapshot together. Computation-forwarding preservation,
full inference/evaluator, Simple-sub A/B remain OPEN 0→0; R50 remains
NOT_ADOPTED.

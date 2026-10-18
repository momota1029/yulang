# Implementation handoff — rejected Replay constructor observation

Status: implementation complete; stopped before build/test/runtime for the
required fresh instrumentation review. This is provisional source-evidence
instrumentation and does not close `CHOOSE-SOURCE-2 /
RECEIVE-NEGATIVE-PAIR` (still OPEN, closure 0).

## Exact artifact and specimen

- Test: `candidate_scheme::authentic_demand_capture_tests::replay_constructor_lineage_observes_rejected_cross_route_authentication`.
- Exact fixture: the previously pinned `demand-route-auth` source specimen used
  by the rejected authentication diagnostic.
- Source addition: only the distinct `#[test]` function in
  `crates/yu-solver/src/candidate_scheme.rs`.
- Current `candidate_scheme.rs` SHA-256:
  `08fab00cc7b7c4d765a1755e582a78bf045f186241c37d7385060a2b47f59fe6`.
- Removing only the added function reconstructs the explicit scheme baseline
  byte-for-byte: SHA-256
  `b05bbf4d683df4d8c520ab215770dc33545225484c626ec82c17e06779db8cbc`.
- Read-only `candidate_context.rs` remains SHA-256
  `22a42a41253161f33d68f9670ee64868c684c99bc692380c018f76a013abe147`.

## Observations emitted by the test

The new test performs ordinary candidate inference and emits Module route 0/use
1 and route 1/use 2 identities, full capture and reconstruction row metadata,
canonical-map hit/miss and insertion-order fields, and complete row images. It
also emits the Replay row, lower Relation58 provenance/emission evidence,
upper/child relation lineage, source/native/copy/lower Function roots and
ordered ports, and each ordered FunctionPort's matching relation IDs, endpoint
pairs, and source ancestry. Replay drain receipts are emitted as observed
receipts or `NotRetainedReachabilityUnknown`; absence is not described as
`NotReached`. Authentication is observed through the diagnostic callback and
the test requires the result to be `None`.

All classification output is emitted before assertions depending on the
authentication result. The test does not call `expect` on successful
authentication, alter authentication behavior, or mutate fixture/control
state.

## Verification and stop boundary

- Verified source-only by reconstructing the pinned scheme baseline after
  removing the one test addition.
- Verified the context source hash remains pinned.
- No build, test, runtime, or Cargo command was run in this lane.
- No scratch or other paths were created.
- Fresh instrumentation review must check test-only containment, preserved
  baseline bytes and old assertions, pre-authentication output ordering,
  FunctionPort/map edges, and the source-grounded drain classification. Only
  CLEAN authorizes the one exact invocation specified in the sprint contract.

## Open source-evidence TODOs

- Independently determine whether the four route-derived FunctionPort pairs
  have retained `FunctionPort` relation IDs in this rejected execution; a
  missing pair must remain a failed observation, not be inferred from root
  shape or the authentication failure.
- Review whether the captured drain receipts provide matched child identities
  and actual return completion. If observations are absent, reachability stays
  unknown.
- Keep the source/native correspondence observational and conditional. This
  handoff proves neither ownership alternative, universal receive transport,
  original `?e_Op`, F1/FK1, Call, soundness, principality, nor termination.

Next related step: fresh instrumentation review of the frozen source addition;
then, only on CLEAN, one exact test execution and runtime receipt under the
Luna-owned runtime lease.

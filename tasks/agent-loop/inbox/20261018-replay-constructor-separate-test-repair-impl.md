# Frozen implementation handoff — Replay constructor observation repair r5

Sprint: `npair-replay-constructor-lineage-20261018-r5`, revision 5
Contract SHA-256: `d58b01bc34761cffe1120fc2d2f2f74371dd4308cd91b6c1507c22aa0d851d20`
Assignment: r5 implementation repair, handoff revision 1
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, still OPEN, closure 0.

## Frozen artifacts and baseline

- `crates/yu-solver/src/candidate_scheme.rs`, SHA-256
  `5e8060b6e717adb5e10c47d8e0cba2ba532b0cef85842b580980cc4a2af266b1`.
- Removing only the repaired test function reconstructs the pinned r4 scheme
  baseline byte-for-byte, SHA-256
  `b05bbf4d683df4d8c520ab215770dc33545225484c626ec82c17e06779db8cbc`.
- Read-only `candidate_context.rs` remains SHA-256
  `22a42a41253161f33d68f9670ee64868c684c99bc692380c018f76a013abe147`.
- Prior r4 implementation handoff:
  `tasks/agent-loop/inbox/20261018-replay-constructor-separate-test-impl.md`,
  SHA-256 `a979c08e8fa3b38200896d32041b6b9601e7428f3af7417427243ad235996901`.
- No other source, scratch, or generated paths were written.

## Repair outcome

Only the existing r4 test function
`candidate_scheme::authentic_demand_capture_tests::replay_constructor_lineage_observes_rejected_cross_route_authentication`
was modified. It now prints keyed route observations without zip truncation,
then asserts exact route/use identities, nonempty complete row counts, row
indices, and equality between each reconstruction image and its full row image.
It requires exactly one Replay row for call 0 and an actual native call before
the final authentication-`None` assertion can pass.

Each FunctionPort observation is now selected by the target Replay child's
parent identity, exact typed endpoint pair, and field. The assertions require
one edge for each ordered field, operations
`[Swap, Swap, Preserve, Preserve]`, and four distinct child relation IDs.
The lower producer path requires retained source occurrence ancestry and a
relation-keyed admission whose retained emission includes physical readback
at `ConstructorAfterAppend`.

Drain output is classified as matched only for a unique child-return receipt
for the selected child, with its acknowledgement tied to the same Replay
operation, `ReturnReady` stage, and a unique complete drive return whose
operation state is retired/idle with queued equal to consumed. Missing,
duplicate, or unmatched receipts print
`NotRetainedReachabilityUnknown`; this test has no `NotReached` inference.
Evidence is printed before assertions, and missing prerequisites fail their
own explicit assertions instead of making a missing authentication attempt
look like an observed `None`.

## Reused evidence, checks, and limits

The repair consumed the exact r4 BLOCKING findings recorded in the r5
contract/current state: selected-child port identity/operation/uniqueness,
matched target drain acknowledgement/return, and explicit observation
completeness. It reused the r4 rejected source snapshot and existing
`test_relation_lineage`, `test_provenance_for_relation`, dependency, and drain
observation accessors. It did not restore a Simple-sub bypass or change
authentication behavior, mutation controls, source fixture, expectations,
or `candidate_context.rs`.

Checks performed: `git diff --check` for the leased source and an in-memory
SHA-256 reconstruction after deleting only the test function. Both passed.
No test, build, runtime, Cargo process, or old-test invocation was run. The
420-second implementation cap was respected; exact active seconds were not
reported by the runtime. Requested model/effort: Luna/high. Observed
model/effort: UNKNOWN.

This remains provisional source-evidence instrumentation. It does not show
that a run passes, prove either ownership alternative, establish a source/native
theorem, or close the original parent. A fresh instrumentation reviewer must
review these frozen bytes before Luna's separately authorized exact run.

Next related step: independent review of this exact test-only addition against
the r4 baseline and the r5 child/port/drain/completeness criteria. Writer state:
STOPPED; writes ended at this frozen handoff. No descendants or unresolved
leases.

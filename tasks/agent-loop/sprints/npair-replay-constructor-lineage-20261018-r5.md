# Repair the isolated Replay observation test

This revision follows the r4 **BLOCKING** instrumentation review. The explicit
r4 source baseline remains authoritative for this test-only packet. Original
parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains **OPEN**,
closure **0**, with fixed `c`, original quantifiers, source domain and accepted
semantics unchanged. No production changes. Astra 0.

## Fixed outcome

Repair only the new test function so a passing run establishes complete,
identity-linked observations for the already rejected cross-route specimen.
Preserve the old test, every authentication implementation byte, all mutation
controls, and the r4 baseline outside this one function.

The exact full path remains:

`candidate_scheme::authentic_demand_capture_tests::replay_constructor_lineage_observes_rejected_cross_route_authentication`

The new test must select exactly one target Replay row and establish:

1. Native call and required provenance/readback/ancestry exist.
2. Module route0/use1 and route1/use2 each have nonempty, keyed, complete row
   observations. No zip truncation, equal-empty counts, or unkeyed aggregates.
   Capture records are insertion-only; absent alias events prove nothing.
3. Each of the four FunctionPort edges belongs to the selected child: match
   `parent == target_row.child`, exact endpoint pair, exact field, and exact
   operation `[Swap, Swap, Preserve, Preserve]`. Require exactly one edge per
   field and four distinct child relation IDs.
4. Lower Relation58 producer, nonempty occurrence ancestry, admission,
   physical emission and readback form the exact linked path.
5. Drain/return evidence matches the selected child, Replay operation and
   acknowledgement, then its drive return. Unrelated global receipts cannot
   count. Missing or unmatched receipts mean
   `NotRetainedReachabilityUnknown`; `NotReached` requires direct control-flow
   evidence.
6. Only after collecting and printing evidence may the test assert that this
   selected authentication attempt returns `None`.

Missing native/provenance/ancestry must fail explicitly and cannot synthesize
the expected `None`. The test must emit observations before its final
assertions. Authentication failure by itself establishes neither sharing nor
lost fresh separation.

## Frozen pins

- r4 contract SHA-256:
  `1eed76f1c8d9f9fb115a1f2a26a9845da230e7c17762cf3350d691190f43c049`.
- r4 scheme-entry bytes SHA-256:
  `08fab00cc7b7c4d765a1755e582a78bf045f186241c37d7385060a2b47f59fe6`.
- Removing only the r4 test addition recovers scheme baseline SHA-256:
  `b05bbf4d683df4d8c520ab215770dc33545225484c626ec82c17e06779db8cbc`.
- Context bytes SHA-256:
  `22a42a41253161f33d68f9670ee64868c684c99bc692380c018f76a013abe147`.
- CLEAN prior audit note/handoff hashes remain in r4.
- Conditional proof source draft SHA-256:
  `290018128ebd6a685186b1eb9d4d3481b7a332780a454c7bbe95dcdfaea99fce`.
- Prior BLOCKING review handoff is recorded in current state and must be
  consumed exactly: selected-child port identity/operation/uniqueness,
  matched target drain evidence, and explicit observation completeness.

Verify all pins at intake; stop on mismatch. The r4 rejected source snapshot
is the starting point; do not reconstruct the older pre-r2 source.

## Exact paths and leases

Implementation (`implementer`, Luna/high):

- `crates/yu-solver/src/candidate_scheme.rs` — modify only the r4 test function.
- `tasks/agent-loop/inbox/20261018-replay-constructor-separate-test-repair-impl.md`.

`candidate_context.rs`, r4 snapshot files, prior tests and all auth code are
read-only.

Proof (`prover`, Sol/high):

- `notes/theory/2026-10-18-replay-constructor-separate-test-recovery.md`.
- `tasks/agent-loop/inbox/20261018-replay-constructor-separate-test-recovery-proof.md`.

Luna:

- `tasks/agent-loop/current.json`.
- `tasks/agent-loop/runtime/20261018-replay-constructor-separate-test-r5.stdout.log`.
- `tasks/agent-loop/runtime/20261018-replay-constructor-separate-test-r5.stderr.log`.
- `tasks/agent-loop/runtime/20261018-replay-constructor-separate-test-r5.meta.json`.

No other writes, scratch paths, dependencies, descendants, old test execution or
production/authentication changes.

## Review and single-run gate

Freeze implementation, handoff and the exact r4 baseline before review. A fresh
instrumentation reviewer checks only this test addition: deleting the new test
must reproduce the r4 scheme SHA byte-for-byte; context must remain unchanged;
every relation must be identity-joined to the selected child, field and
operation; every observation assertion must reject missing/ambiguous data; and
drain receipts must match target child, operation, acknowledgement and drive
return. CLEAN only authorizes one full-path new-test invocation using
`--exact --nocapture`.

No retries, old-test execution, broad suite or unrelated build. Capture
executable and source hashes, command, stdout, stderr and exit status. After
the run, freeze proof note and both handoffs; a different fresh reviewer
checks the source, runtime, and proof artifacts. No reviewer authors either
lane.

## Budget

Fresh r5 envelope **1140s**, no rollover from r4:

- implementation420s;
- proof180s;
- instrumentation review120s;
- one exact runtime120s;
- final review180s;
- Luna integration120s.

Astra 0, descendants 0, one Cargo process maximum. Prior r4 consumed580s and
expired500s remain recorded separately. Preserve original parent closure **0**
unless an original theorem obligation is genuinely proved.

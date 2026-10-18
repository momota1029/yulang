# Repair the two remaining Replay observation checks

Revision 6 follows the r5 **BLOCKING** instrumentation review. It keeps the
original parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` OPEN at
closure **0**, preserving fixed `c`, original quantifiers, source domain and
accepted semantics. This packet adds only test-only source observation; it
does not alter authentication, solver behavior, or production policy. Astra 0.

## Fixed outcome

Repair the two exact r5 findings as one bounded source-evidence result:

1. FunctionPort uniqueness must be checked over every edge with the selected
   Replay child's `parent` and requested `field`, before endpoint-pair and
   operation checks can filter conflicting edges.
2. Producer provenance must join the selected relation to typed admission and
   emission records, then compare complete `BoundKey`, physical slot, readback
   slot, and readback phase. Debug-text substring presence is insufficient.

Keep r5's row completeness, target identity, drain linkage and before-assertion
output requirements. Missing or ambiguous evidence fails explicitly. Missing
drain linkage remains `NotRetainedReachabilityUnknown`; do not infer `NotReached`.

## Frozen dependencies

- r5 contract SHA-256:
  `d58b01bc34761cffe1120fc2d2f2f74371dd4308cd91b6c1507c22aa0d851d20`.
- r5 source SHA-256:
  `5e8060b6e717adb5e10c47d8e0cba2ba532b0cef85842b580980cc4a2af266b1`.
- r5 implementation handoff SHA-256:
  `4e3555e7a9b348a849e177062a54b9b763c74fe12c444de177159fd5f00b4bd8`.
- r5 context baseline SHA-256:
  `22a42a41253161f33d68f9670ee64868c684c99bc692380c018f76a013abe147`.
- r4 test-removal scheme baseline SHA-256:
  `b05bbf4d683df4d8c520ab215770dc33545225484c626ec82c17e06779db8cbc`.
- Conditional proof input:
  `notes/theory/2026-10-18-replay-constructor-separate-test-recovery.md`,
  SHA-256 `ba6f2d7a0dc48c9d03038cccb17d8b5a98800ab8f72222b4e57302246aa4784a`;
  handoff SHA-256
  `accb400675f9a12e90dbf4c9f2a43f85bc7924c10f0942cda2417249bab93483`.
- Fresh r5 review: BLOCKING on uniqueness ordering and typed producer identity;
  no source writes or execution.

Verify every pin at intake. Deleting only the test addition from
`candidate_scheme.rs` must recover the exact r4 scheme baseline. Removing only
the new `#[cfg(test)]` accessor from `candidate_context.rs` must recover the
exact r5 context baseline.

## Lanes and exact leases

**Implementation — Luna/high, 300 seconds:**

- `crates/yu-solver/src/candidate_scheme.rs`: modify only the r5 test function.
- `crates/yu-solver/src/candidate_context.rs`: add one `#[cfg(test)]`
  read-only accessor returning structured admission records for a relation and
  their exact associated emissions. It must expose only existing retained
  values and add no storage or production behavior.
- `tasks/agent-loop/inbox/20261018-replay-constructor-r6-impl.md`.

The port query first gathers all `FunctionPort` dependencies whose parent is
the selected child and whose field is the requested field; assert cardinality
one before checking that edge's exact pair and `[Swap, Swap, Preserve,
Preserve]` operation. Require four distinct child relation IDs.

The typed producer accessor must preserve admission/emission IDs and records.
The test must select the unique relation-keyed admission/emission chain for
the lower producer and compare its complete bound identity to the selected
producer key, emission bound to admission bound, physical slot to readback
slot, readback bound to the same complete key, and phase to
`ConstructorAfterAppend`. Print the complete structured records before the
final assertions. If existing data cannot provide these exact joins without
changing semantics or expanding the two code leases, stop with the first
missing field and do not add another hook.

Preserve the old test, fixture, authentication and mutation controls. No other
source edits, scratch paths, generated changes, builds or tests during authoring.

**Proof — Sol/high, 120 seconds:**

- `notes/theory/2026-10-18-replay-constructor-r6-parent-application.md`.
- `tasks/agent-loop/inbox/20261018-replay-constructor-r6-proof.md`.

Reuse C1-C4 only conditionally. Verify the new accessor's exact source
coverage, apply no unobserved runtime claim, and state the first still-missing
original-parent premise. Sharing/lost separation remains undecided absent a
reviewed runtime result. Parent closure remains 0.

**Luna runtime outputs:**

- `tasks/agent-loop/runtime/20261018-replay-constructor-r6.stdout.log`
- `tasks/agent-loop/runtime/20261018-replay-constructor-r6.stderr.log`
- `tasks/agent-loop/runtime/20261018-replay-constructor-r6.meta.json`

## Review and execution gates

Freeze source, both handoffs, proof and direct dependency hashes. Obtain a fresh
read-only instrumentation review, cap 120s. Only CLEAN authorizes one exact
invocation of
`candidate_scheme::authentic_demand_capture_tests::replay_constructor_lineage_observes_rejected_cross_route_authentication`
with `--exact --nocapture`, cap 120s. Capture command, source/executable
hashes, stdout, stderr and exit status. No retry, old-test invocation, broad
suite, or parallel Cargo process.

After the run, a different fresh reviewer checks frozen source, runtime and
conditional parent application, cap 180s. Luna integrates/state/Git within
120s after accepted evidence. CLEAN instrumentation and a passing test do not
close the parent theorem or authorize production changes.

## Budget and stop conditions

r5 spent 720s (implementation420, proof180, instrumentation review120); its
unused420s expire and do not roll over. Fresh r6 budget **960s**:

- implementation300s;
- proof120s;
- instrumentation review120s;
- one exact runtime120s;
- final review180s;
- Luna integration120s.

Combined r5+r6 cap: 1680s. Astra0. Stop on any pin mismatch, required scope or
semantic expansion, missing structured owner data, review finding outside
these two repairs, exact-test failure, or exhausted grant. Preserve the parent
claim and all unresolved conditions unchanged.

# Recovery sprint — isolate and observe rejected Replay lineage

This revision follows the BLOCKING instrumentation review under r2. Original
parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains **OPEN**;
closure **0**. Preserve original quantifiers, source domain, accepted
semantics and fixed `c`. No authentication semantics or production behavior
changes are authorized. Astra **0**.

## Fixed outcome

First establish byte-level provenance for the r2 source change. Then add a
distinct test path that observes the rejected cross-route specimen before or
independently of the known failed authentication, while preserving the old
test, its assertion and mutation controls. The new test must pass only when it
identifies both Module route0/use1 and route1/use2, reports construction and
canonical-row hit/miss evidence, traces relation/admission/emission and all
ordered ports, and states whether Replay drain completed or was not reached.

No rerun of the old exact test, no retry, no broad suite, and no test/build/
runtime until fresh independent CLEAN instrumentation review. If the required
test-only isolation, baseline provenance, or bounded source trace cannot be
established within the assigned stage, STOP and report the exact missing fact.

## Previous review and pins

- r2 contract SHA-256:
  `b04f61d76511ebca81ed5217bf8ba0ec76fdaa3035a212123031e4079005ad80`.
- Previous CLEAN ownership audit: note
  `572884a8df2e8adc19eb1a8121277c77784e3c02fa9925729e292dd629f40308`,
  handoff `f2c93d65ba96e4a256010e2942096ca21ef714b5b06d81573701eb0b960948ed`.
- Frozen BLOCKING implementation handoff:
  `tasks/agent-loop/inbox/20261018-replay-constructor-lineage-impl.md`
  SHA-256 `292b828fe891a69f194e9872826cc0baaa9443db6f65a1aeb8caaecd3cd07274`.
- r2 input bytes to recover exactly:
  `candidate_scheme.rs` SHA-256
  `0c55d3d47bc88166a68eb5f5797043b136a2d2bc0ace55de832e8e27ca20a07f`,
  `candidate_context.rs` SHA-256
  `f2ecbadcc33e4439c57429cb6a6ce5bcdfd5c3131f5b5ebb9d1e03a0e224f569`.
- r2 rejected output bytes currently frozen:
  `candidate_scheme.rs` SHA-256
  `b05bbf4d683df4d8c520ab215770dc33545225484c626ec82c17e06779db8cbc`,
  `candidate_context.rs` SHA-256
  `22a42a41253161f33d68f9670ee64868c684c99bc692380c018f76a013abe147`.
- Existing diagnostic runtime remains pinned in r2. It already establishes
  that the old test path fails at authentication; do not rerun it.

At intake, verify every listed hash. Preserve source snapshots before any
mutation. First-stage recovery must produce byte-identical r2 input snapshots;
otherwise STOP without overwriting source. The original local HEAD is known to
be stale and does not substitute for either pinned input.

## Exact paths and leases

Implementation author, exact writable paths:

- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/candidate_context.rs`
- `tasks/agent-loop/runtime/20261018-constructor-recovery.candidate_scheme.before.rs`
- `tasks/agent-loop/runtime/20261018-constructor-recovery.candidate_context.before.rs`
- `tasks/agent-loop/runtime/20261018-constructor-recovery.candidate_scheme.rejected.rs`
- `tasks/agent-loop/runtime/20261018-constructor-recovery.candidate_context.rejected.rs`
- `tasks/agent-loop/inbox/20261018-replay-constructor-lineage-recovery-impl.md`

Proof author, exact writable paths:

- `notes/theory/2026-10-18-replay-constructor-lineage.md` (existing draft; do
  not claim frozen status until post-run evidence is incorporated)
- `tasks/agent-loop/inbox/20261018-replay-constructor-lineage-recovery-proof.md`

Luna integration and the one authorized runtime attempt:

- `tasks/agent-loop/current.json`
- `tasks/agent-loop/runtime/20261018-replay-constructor-lineage.stdout.log`
- `tasks/agent-loop/runtime/20261018-replay-constructor-lineage.stderr.log`
- `tasks/agent-loop/runtime/20261018-replay-constructor-lineage.meta.json`

All other paths are read-only. No dependency changes, scratch paths,
descendants, authentication relaxation, semantic rules, or broad fixture edits.

## Required implementation

Stage 1 is limited to 180s of the implementation envelope. Recover the exact
r2 input source bytes into the two `.before.rs` snapshots, and copy the exact
BLOCKING output bytes into the two `.rejected.rs` snapshots. Verify all four
hashes. If the two before snapshots cannot be recovered byte-for-byte within
180s, STOP; do not reconstruct by guess, overwrite the sources or proceed to
test execution.

After successful recovery, compare the exact before/rejected bytes and
separate r2-introduced changes from prior working-tree state. Preserve the
original failing test, assertions and mutation controls. Add a new distinct
full path:

`candidate_scheme::authentic_demand_capture_tests::replay_constructor_lineage_observes_rejected_cross_route_authentication`

The new test must retain its own passing contract: both exact route/use IDs;
capture/reconstruction representative and metadata; canonical_rows hit/miss
and first insertion order; complete per-route row images; lower producer,
source occurrence ancestry, admission and physical emission; upper and lower
ordered ports with exact child RelationIds; Replay ancestry and actual drain
outcome, including an explicit `NotReached`/`NotRetained` result if failure
prevents drain. Emit records before interpreting failed authentication; never
gate observations on `evidence.expect(...)`. Assertions may establish that
this specimen is rejected, but may not weaken the existing authentication or
its assertion. No auth predicate/wrapper/refactor may be changed by this stage;
existing production code is baseline only after the byte snapshots and diff
classification succeed.

## Proof lane

Use the existing source-level C1–C4 draft as conditional work, not frozen
evidence. Refine the canonical_rows hit/miss induction, connect exact
source/runtime events only after fresh review, and classify shared borrowing,
lost fresh separation or the first still-missing fact. State explicitly when
the drain was unreachable. Keep original parent OPEN and closure 0. This
specimen does not prove universal receive transport or original `?e_Op`.

## Independent review and one-run gate

Fresh instrumentation review before the run: check exact source snapshot
hashes, provenance of every changed hunk, distinct test identity, pass/fail
semantics, cfg(test) containment, unchanged existing auth and mutation
controls, complete pre-auth observations, and no production change. Only
CLEAN authorizes one full-path new test invocation with `--exact --nocapture`.
The new test must be selected exactly once. Capture executable/source hashes,
stdout, stderr, command and exit status. No retries or old-path execution.

After the run, freeze the proof note and handoffs. A second fresh independent
review checks frozen code, proof and runtime. Reviewers author neither lane.

## Budget and stop conditions

New envelope **1200s**, with no rollover from r2: provenance recovery 180s,
implementation 360s, proof 180s, instrumentation review 120s, one exact
run 120s, final review 120s, Luna integration 120s. Astra 0; no descendants;
one Cargo process maximum. Preserve prior r2 charges and its unused-budget
expiration separately.

Stop on any hash mismatch, inability to recover the exact before bytes within
180s, path/lease conflict, production auth change, missing test distinction,
observation that still occurs after a failing assertion, unexpected runtime
failure, or new semantic choice. No theorem closure is awarded for diagnostics.

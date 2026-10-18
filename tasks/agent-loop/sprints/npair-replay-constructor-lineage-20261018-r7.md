# Require unique relation-level Replay producer evidence

Revision 7 is a single bounded repair after r6's fresh **BLOCKING** review.
The original parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` stays
OPEN at closure **0**; fixed `c`, quantifiers, source domain and accepted
semantics do not change. No proof, production, or runtime conclusion is
authorized by this source repair.

## Exact outcome

The r6 test currently filters relation-keyed admissions by the expected
`BoundKey` before checking uniqueness. A conflicting admission for the same
relation can therefore be discarded. Modify only the existing new test in
`candidate_scheme.rs` to assert exactly one admission over the complete
relation-keyed set first. Then compare that admission's complete bound and
preserve r6's exact emission/readback/slot/phase assertions. Keep all
observations before the final assertion and preserve the existing accessor,
port checks, drain classification, fixture, authentication code and mutation
controls.

The falsifier is a relation with two admissions, one matching the target
BoundKey and one conflicting: the test must reject it. No new accessor or
source hook is authorized. Any other finding or unavailable exact relation
evidence ends this repair without further extension.

## Frozen dependencies

- r6 contract SHA-256:
  `68a518fa706613d523a9fe3a6be2394fb491e132e048b1299144532258d85fff`.
- r6 scheme SHA-256:
  `d8c53522685e9bdfc1ba00380f222f4936d8d8df3302248fcde31e093668c484`.
- r6 context SHA-256:
  `42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca`.
- r6 implementation handoff SHA-256:
  `b4363b959ae7ab06696cc977da94819ce6c24e5642a5e0674bf9d538726c802e`.
- r6 conditional proof SHA-256:
  `8d5cab69798da42c9de464f5dc8d568d647f3fa98e6d028289c8310e6b87d49c`;
  handoff SHA-256
  `b7955905761ccc5f90cb294e1e3f012b7278cf7c95509d2c6610a3a79b8dc4a8`.
- r6 review BLOCKING: relation-wide admission cardinality must precede
  BoundKey filtering. Port uniqueness, structured emission/readback checks,
  both baseline reconstructions and observation ordering were accepted.
- Test-removal scheme baseline SHA-256:
  `b05bbf4d683df4d8c520ab215770dc33545225484c626ec82c17e06779db8cbc`.
- Accessor-removal context baseline SHA-256:
  `22a42a41253161f33d68f9670ee64868c684c99bc692380c018f76a013abe147`.

Verify every pin at intake and after the edit. Only the test function may
change; deleting it must recover the scheme baseline byte-for-byte. Context
must remain at the pinned r6 hash.

## Lanes and exact leases

**Implementation — Luna/high, 90 seconds:**

- `crates/yu-solver/src/candidate_scheme.rs`, only the new test function.
- `tasks/agent-loop/inbox/20261018-replay-constructor-r7-impl.md`.

No `candidate_context.rs` writes, no test/build/runtime during authoring, and
no unrelated source edits. Freeze hashes and stop writes at the bound.

**Proof:** reuse the frozen conditional r6 proof; no new proof authoring or
lease. C1-C4 remain conditional and the original parent remains OPEN.

**Luna runtime outputs:**

- `tasks/agent-loop/runtime/20261018-replay-constructor-r7.stdout.log`
- `tasks/agent-loop/runtime/20261018-replay-constructor-r7.stderr.log`
- `tasks/agent-loop/runtime/20261018-replay-constructor-r7.meta.json`

## Review and execution

Obtain a fresh read-only delta instrumentation review, cap 90s. CLEAN permits
one exact invocation of
`candidate_scheme::authentic_demand_capture_tests::replay_constructor_lineage_observes_rejected_cross_route_authentication`
with `--exact --nocapture`, cap 120s. No retry, old-test invocation, broad
suite or parallel Cargo process. Capture the command, source/executable hashes,
stdout, stderr and exit status.

After the run, use the reserved fresh final-review allocation of 180s for the
frozen implementation, runtime and conditional proof application. Luna has
120s for integration/state/Git. These stages do not close the original parent
or authorize production changes.

## Budget and stop conditions

r6 charged 540s (implementation300, proof120, instrumentation review120).
Its remaining runtime120, final review180 and integration120 stay reserved.
This r7 grant adds **180s**: implementation90 and fresh delta review90. Combined
r6+r7 cap is **1140s**, with 600s remaining at r7 start; combined r5+r6+r7 cap
is **1860s**. Astra0; no rollover or automatic renewal.

Stop on any pin mismatch, any additional finding outside relation-admission
uniqueness, exact-test failure, semantic/scope expansion, or exhausted grant.
No further instrumentation cycle is authorized by this contract.

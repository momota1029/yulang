# Outcome — NATIVE-COMPLETED-EMISSION-READBACK/r3

Status: **CLOSED_INCOMPLETE / REJECTED**. This record preserves a bounded
research result and its non-waivable deviation. No compiler, Cargo, Lean, Lake,
test, formatter or checker execution was authorized or performed after review.

## Fixed parent and authority

The sprint preserved the original
`YulangClosure.SourceProblem.InferenceSoundness` quantifiers and supported-source
domain:

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

Lawful finite histories, retained extrusion occurrences, the shared witness,
source/native correspondence, Simple-sub A/B, effect hygiene, principality,
termination and executor obligations remain **OPEN**. The approved effect
policy was not changed. No production or semantic authority was granted.

Base contract:
`tasks/agent-loop/sprints/native-completed-emission-readback-20261028-r3.md`,
SHA-256 `d1c194c85c54d7ea2016c64e60d51d7805e480ae7c824b167f0bc86fee94d71e`.

Amendment 01:
`tasks/agent-loop/sprints/native-completed-emission-readback-20261028-r3-amendment-01.md`,
SHA-256 `2cb2c017b5028c382c82f55ad9efad1b278be13070a9aeb979a32992e096ad4f`.
It pinned `candidate_intrusion.rs` as read-only at
`475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` with a
strict scope limited to the settle path and same-file write-determining callees.

## Proof lane and non-waivable deviation

Proof handoff r1 is preserved unchanged at
`tasks/agent-loop/inbox/native-completed-emission-readback-r3-proof.md`,
SHA-256 `c71c79cc623bbaa95247925ce4bfc5f780578caf736c53c7e1a619fa12cc3ccd`.
Before Amendment 01 it identified an unpinned child writer and stopped before
reading that body. No Lean module or theorem was produced. No Lean/Lake version,
type or axiom audit exists for this sprint.

After ACKing Amendment 01, the proof worker requested
`candidate_intrusion.rs` lines 400–568. The returned range also displayed
unrelated `mark_candidate_pair` and `journal_candidate_memo` bodies around
lines 426–505, outside the amended scope. The worker stopped immediately. No
further source reads, proof construction, writes, checks or builds followed.
This is a non-waivable deviation under the fixed contract. R3 acceptance cannot
be restored retroactively. The worker's read-scope report and STOPPED receipt
were recorded in current state; the original r1 handoff bytes were not edited.

The bounded report noted a forest write at `candidate_intrusion.rs:560` and a
bound-append path at `:657` through pinned extrusion code. These are only
unverified investigative leads, not a preservation proof, accepted source
evidence or a source-qualified counterexample.

## Rust lane and independent review

Frozen Rust handoff:
`tasks/agent-loop/inbox/native-completed-emission-readback-r3-rust.md`,
revision 1, SHA-256 `66dbd90db2c1e21d5277761ab2f48ca34b456bcd54ea8abc204a35f642290341`.

Frozen provisional artifacts:

- `isolated/native-completed-emission-readback-r3/crates/yu-solver/src/candidate_scheme.rs` — `75242b9bdf8aad67938501bd4a06f5202a65675da694ab77a80b77592076c83c`
- `isolated/native-completed-emission-readback-r3/crates/yu-solver/src/candidate_extrusion.rs` — `abf8ffd0624f7553acc186e232c42623ba99a9cce49102e54bc7e2d3d8ea1817`

The source adds `cfg(test)` recording of the driver's returned emission,
post-driver access to current relation/flow/raw transformer and a reread through
the existing physical-slot reader. It keeps mapped and admitted IDs separate,
includes scoped/unscoped fixtures and treats transformer root zero as logical
identity. These are source assertions only; they are not passing runtime
evidence. The handoff itself records that the new completed-chain predicate has
not been exercised against the named mutations.

Fresh read-only review by `/root/native_completed_emission_readback_r3_review`
returned **REJECT**. Requested `gpt-6.1-sol / medium`; observed model/effort
UNKNOWN. No checks, writes or Git operations occurred. The independent findings:

1. **BLOCKING — the test source has a non-exhaustive tuple match.**
   `candidate_extrusion.rs:719` covers eight same-kind owner/lane pairs but not
   the other valid `RowKey × BoundLane` combinations. Review predicts an E0004
   compile failure; this was not confirmed by a compiler.
2. **BLOCKING — a shared context borrow crosses mutation hooks.**
   `candidate_scheme.rs:7824–7825` retains an immutable context borrow that is
   reused inside the emissions loop, while later loop operations mutably borrow
   the same context. Review predicts E0502; no compiler was run.
3. **major — the new completed predicate does not bind invocation ownership.**
   It ignores `returned.invocation`; emission IDs may be permuted across
   invocation records while uniqueness still holds. A sibling emission can
   satisfy the `.any` association. The mutation assertions use the older
   `authenticate_demand_transport` predicate and precomputed `completed_bindings`,
   so they do not establish rejection at the new completed join for the required
   antecedent/emission/mapped-admitted/duplicate/flow/slot mutations.
4. **BLOCKING — no successful child-preservation bridge exists.** The proof
   handoff has no declarations, and preservation through the settle/child path
   is unproved.
5. **BLOCKING — the proof-lane scope deviation disqualifies the fixed packet.**
   This finding alone makes combined R3 acceptance ineligible.

Review considered the Rust slice technically useful as provisional instrumentation
but not a credible executable package in its frozen form. Reviewer details and
the source-derived nature of compile findings are preserved in its final
message; Rust source was not built or tested.

## Execution, resources and remaining work

Cargo, Lean/Lake, builds, tests, formatters and sprint checker were **not run**
for artifact correctness. The static agent-state checker passed after current
state updates; it validates scheduling records only. No runtime output or theorem
type/axiom audit exists. Worker model observations and active-time measurements
remain UNKNOWN where receipts did not provide them. No descendant or background
work remains active.

R1's non-waivable pin-order deviation and R2's read-only Git deviation remain
preserved as prior incomplete outcomes. No waiver was granted. UNKNOWN worker
observations, quarantined path leases and the prior capacity-only override were
left unchanged.

The next eligible packet must repair the test-only source issues, tie each
invocation to its actual returned emission and source witness, test each required
mutation against the full completed readback predicate, and construct a checked
preservation bridge from the actual child writer branches. Any new source owner
must be pinned before body reads. Original parent and production gates stay
OPEN until their separate obligations close.

# Sprint FORMAL-PERMISSION-PROJECTION-20261028/r8 amendment 03

This sequential amendment preserves original r8, amendments 01–02, the frozen
r8-r3 source handoff and its independent review. It adds one source owner and
repairs a gap in the conditional composition identified by the reviewer. The
original goal, accepted semantics, source/native scope and open parent gates do
not change.

## Frozen evidence and adjudicated review finding

- Amendment 02: `tasks/agent-loop/sprints/formal-permission-projection-20261028-r8-addendum-02.md`, SHA-256 `c50bb1d2f500f6604eab456de1ea8c157415ed608518c5ff3be54e675aa3f7fc`.
- Reviewed source: `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r3.md`, SHA-256 `aafd543e2dc727d8999342ff0d76b8419730befd48cbf9a2d8cd6116a0771148`.
- Independent review: `tasks/agent-loop/inbox/formal-permission-projection-20261028-review-r8-r3.md`, SHA-256 `19aabd5cee2cd4c92f1bdc7559b60c66022a20403792d70da97a9931538e86f6`.
- Baseline: `3cc8a897fe08980576b1582952a95acab55f09d2`.

The reviewer found a MAJOR gap in the r8-r3 conditional composition: selected
root stability and correct inverse-log ordering do not exclude an intervening
helper from creating a cycle among other roots. The root-link lemma requires a
closed finite forest immediately before the link. Correct inverse logging
supports rollback but proves neither forward closure nor absence of unrelated
cycles. Preserve the r8-r3 inventory, but do not rely on its claimed
composition; this amendment does not close the forest premise.

## Exact new owner and authentication

The new unadmitted owner is
`crates/yu-solver/src/candidate_context.rs`. Its exact baseline Git blob at
`3cc8a897fe08980576b1582952a95acab55f09d2` hashes to
`57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`.
The worker must reauthenticate this byte hash and all previously admitted
dependencies—including `candidate_extrusion.rs`—before opening source bodies.
Any mismatch stops the packet.

The only newly admitted source owner is that file at the pinned baseline.
Retain and reauthenticate the original nine r8 source/policy pins, the
candidate_extrusion pin from amendment 02, and all exact contract/outcome/source
and review pins named by amendments 01–02. If another unadmitted body is needed,
stop with its path, callsite and exact unsupported equation. Do not open it.

## Fixed outcome and corrected proof boundary

Investigate the same reachable merge-interval preservation obligation, with
the corrected premises:

1. Immediately before each final parent link at
   `candidate_intrusion.rs:679/:691`, the **whole selected forest** is a closed
   finite forest: every in-range chain reaches a self-root and no cycle or
   invalid parent exists elsewhere in that vector.
2. The two selected entries remain distinct, in-range self-roots through the
   interval, and the vector lifetime/identity remains valid.
3. Every effective mutation has a complete inverse entry in the correct
   temporal order for the same active checkpoint; the association survives
   resource/evidence/context helper calls and rollback.

Trace the context evidence/transport operations reached during the interval,
including `candidate_effect.rs:697`, alongside already admitted
transfer/splice/resource/journal calls. Use actual fields, bodies and callees
to produce effect summaries. Establish either a frame proving both forests
cannot be reached or replaced, or an induction showing that every effective
mutation preserves whole-forest closure. Separately establish selected-root
stability and temporal inverse logging. A signature, receiver type, direct
write scan, selected-root fact, or correct inverse entry alone is insufficient.

Compose only source-established facts with r8-r2's valid local lemmas. If
whole-forest closure immediately before the link remains assumed, state it as
OPEN and remove no r7 premise. A conditional repair of the reviewer’s logical
gap is not source-level preservation.

A source falsifier must show a reachable admitted helper sequence that violates
whole-forest closure, selected-root stability, vector lifetime, or checkpoint
log association before the write. Refuting permission projection still needs a
successful wrong-image export retaining the original occurrence and path.

Keep B, D, reachable forest/lifetime preservation, r1 Lean verification,
original parent A/B, source/native, full inference/executor and production
gates OPEN. No compiler changes or theorem/production promotion are authorized.

## Assignment, output and resources

- Sole source output lease:
  `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r8-r4.md`.
- One read-only registered researcher; no descendants or Astra.
- At most 200 seconds, one CPU, 1 GiB RSS. No tests, builds, probes, Cargo,
  Lean/Lake, compiler edits, Git, network or quarantined paths.
- Stop on a hash mismatch, another unadmitted owner, unsupported preservation
  equation, reachable falsifier or resource bound. Freeze one coherent handoff.
- Fresh non-author `compiler_referee` review of the corrected conditional
  statement, whole-forest effects, both forests, selected roots and checkpoint
  ordering: at most 120 seconds, read-only.

Amendment 02's 5,910-second conservative bound already included its 120-second
review reservation; charge that reservation once. Reserve a fresh 470 seconds
for this amendment: source 200, review 120, primary 100, dispatcher 50. Total
reserved/charged becomes 6,380 / 7,200 seconds, leaving 820 seconds. Do not
reclaim unobserved time or reset previous charges; halt if an omitted grant
invalidates the ledger.

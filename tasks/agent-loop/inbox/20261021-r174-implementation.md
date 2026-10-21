# R174 Luna implementation packet — revision 2 candidate

Sprint: `rollback-inert-forwarding-bridge-20261021-r174`, contract revision 2,
SHA-256 `01df299dfd16276d1c0bfc376946ad0dcab47d92ebb1916307fe36ccc33e28d8`.
Luna/high is the implementation owner and sole Git integrator. Requested and
observed runtime model/effort remain UNKNOWN until a trusted receipt exists.

## Frozen inputs and parent

Keep immutable proof baseline `7ec64a3788175913a2be46331cf0f64c6bd5b407`
separate from activation HEAD `e9a7a4fef3d6872fa0596646393a7c0473b3687b` and
R173's failed candidate. R173 final review and exact findings are in current
state closure and the frozen R173 handoff revision 4. The original theorem and
R171 fixture hashes are pinned in the R174 sprint contract. No R173 proof claim
transfers to edited code.

The proof lane reads only the immutable baseline and R173 snapshots listed in
the sprint contract. Luna may edit the four live solver owners concurrently.
After implementation writes stop, Luna freezes a separate R174 candidate
manifest; the proof lane may then apply its argument to those exact hashes, and
Luna pauses solver writes until that proof lease ends. Snapshot preparation is
charged separately; this implementation grant is 1380 seconds.

## Multi-stage implementation outcome

1. Fix receipt ownership without turning optional observation into a semantic
   error or inference decision.
2. Make receipt completion rollback-safe for pre-existing Origins and retries.
   Prefer append-only completion events under the existing checkpoint frontier,
   or an explicit undo path whose allocation failure only makes observation
   unavailable. Show that missing evidence cannot change solver decisions,
   recovery, diagnostics or publication.
3. Build the real source-to-provider-FreshUse-to-Apply consumer bridge using
   producer order and retained owners. Do not require a later Apply relation to
   have existed in an immutable earlier Capture, and do not replace that check
   with an unsupported boolean or endpoint equality.
4. Expose each link and per-component completeness in the bounded R174
   candidate query/harness source. Keep the R171 fixture unchanged. Stop on the
   first owner that cannot support the chain.

## Luna implementation progress — provisional, not reviewed

The R173 ownership defect is repaired by cloning the non-Copy receipt when a
transactional drain frame is copied into its undo record. Completion no longer
mutates the durable Origin. It appends an optional completion event to the
candidate context; the event vector is checkpointed and truncated on rollback.
Passive receipt bytes are excluded from inference resource-limit accounting so
their presence cannot consume solver budget. If completion evidence cannot
reserve space, the event is omitted and the solver still completes normally;
observation then remains unavailable. The existing state has no separate total
owned-byte tally for this optional vector, so its aggregate memory accounting
remains an OPEN premise. The query consults the event log, so rollback/retry
cannot inherit completion state from a failed attempt.

The actual FreshUse-to-Apply consumer association remains unsupported by these
four leased source owners. In particular, the existing query's requirement
that the later Apply relation occur in the provider's earlier Capture is still
an obstruction, not evidence. The proof lane's immutable-source audit found
that the physical restoration/admission constructor is outside the current
four-owner envelope. Do not mark the consumer join complete, infer it from
endpoint equality, or expand the lease. R174 therefore remains unfinished
research unless the exact join can be supported within the authorized paths.

No compiler, test, evaluator, Yulang2 run or probe was run. This progress is
not independently reviewed and does not close the source/native bridge, the
original theorem, or any parent gate.

## Frozen R174 candidate manifest

Luna stopped solver and harness writes before the proof lane's candidate
application. The proof lane reads this separate read-only snapshot, not the
checkout:

```text
24f480355979ee5d96305a08abf6aab67025ede32c2a1575b779e46f5e23b436  /tmp/r174-inputs/r174-candidate-luna-v6/lib.rs
a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733  /tmp/r174-inputs/r174-candidate-luna-v6/candidate_context.rs
48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25  /tmp/r174-inputs/r174-candidate-luna-v6/candidate_scheme.rs
2b0e46f28c328172477ac263360f4f3d01d27714dc62cd93235b8e3b1fe4e9ff  /tmp/r174-inputs/r174-candidate-luna-v6/shadow_apply.rs
920275d9301ace568634d5c1401f93a9ffc01605a7c562e2d4998e85d1109d3b  /tmp/r174-inputs/r174-candidate-luna-v6/r174_forwarding_bridge.rs
```

This is an unreviewed research candidate, not integrated code. The four solver
owners remain frozen pending the proof result and independent exact-manifest
review. Probe status: `NOT_RUN`; the required complete consumer join is absent.

Wait for the constructive lane's useful findings but do not let it write code
or revise the implementation lease. Apply compatible lemmas within this same
envelope. Parent theorem, source/native correspondence and production gates
remain OPEN absent independent closure.

## Checks and review boundary

No test, compiler/build, evaluator, Yulang2 or probe runs in the implementation
lane before frozen independent review. Static inspection may use only the exact
leased owners. A conditional single inference probe remains possible only after
proof and final code/harness/command reviews are CLEAN and the observation can
discriminate every required source-to-consumer link. Otherwise report NOT_RUN.

Stop if certificate data changes semantics, a transaction path cannot be made
observational, the real consumer bridge has no supported constructor, a writer
conflict appears, a dependency or exact lease changes, or the grant is spent.
Do not modify the fixture, unrelated dirty files or frozen review targets.

On freeze, record exact source/harness/note hashes, authors, requested/observed
runtime, checks, limitations, remaining owner and exact review snapshot here.
Only Luna stages explicit paths and inspects the full outbound range before a
non-forced commit/push. Preserve R173's unintegrated failed candidate as history.

## R174 final review and closeout

Independent exact proof/code review: `NOT_CLEAN` for integration or probe.
Reviewer verified all 11 pinned inputs unchanged at entry and exit. The
ownership move is repaired, and the completion-frontier lemma closes only the
specific stale-Origin retry mismatch under ordinary clone and valid-checkpoint
hypotheses. Remaining premises are:

- same-provider mapped restoration through the actual forwarding Apply demand,
  both ordered Replay inputs and consumed FunctionPorts;
- baseline resource-capacity equivalence and physical accounting of optional
  completion storage;
- receipt/CauseId clone and allocation behavior under failure/unwind.

The reviewer found no parent theorem or A/B closure and no probe authority.
Exact receipt: v6 code hashes above; proof note
`45c9d88653d54f018621525e2318a655fec6425727ff484a33375ccd5062689c`; proof
handoff `d874ae111895ce985e780115e02cca4eb64bcb16f99c1788ac156e69c85cfd2a`;
implementation handoff at review `fdfff8c82894c8b1472e6e62bc57c79d8ca0163880f118a298b08ecb456ddf58`;
contract `01df299dfd16276d1c0bfc376946ad0dcab47d92ebb1916307fe36ccc33e28d8`.
This closeout paragraph was appended after the reviewer stopped.
Reviewer runtime/elapsed UNKNOWN; 300 seconds charged. No compiler, tests,
evaluator, Yulang2, probe or Git ran. Candidate remains frozen and
unintegrated. R174 charged 3480 seconds total; 720 seconds were unissued and
expired at closeout under the no-carryover rule.

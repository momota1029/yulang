# R173 source-drain attribution and consumer join — candidate contract

Status: **REVISION 3 ADOPTED BY LUNA** for the bounded final-review reallocation
below. Revision 2 remains preserved in commit `e9a7a4fef`; its delta review does
not cover the final implementation candidate. The active R173 goal and exact
leases continue. The conditional probe is revoked for this sprint and remains
NOT_RUN.

Branch: `research/simple-sub-intrusion`  
Baseline: `7ec64a378` (R172 reviewed checkpoint)  
Contract revision: 3
Parent theorem: `notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1,6–7,
SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`.

## Original outcome and success evidence

Preserve the original forwarding theorem's source domain, quantifiers, shared
satisfying assignment, open incoming E, arbitrary finite chains/repeated calls/
simultaneous entries and every finite prefix. Do not narrow the accepted source
domain or alter inference semantics. R173 targets the unchanged R171
`terminal`/`relay` fixture and the missing R169/R172 source-fact → selected
seed → provider Capture/own maps → actual forwarding consumer association.

Decisive known owner: `start_typed_drain` calls
`candidate_context_seed_with_formal`, then uses `item.relation.or(seed)`. Replay
children enter with a relation and acknowledgement already present, but still
create an occurrence-matching Origin. R172's exact-hash reviewed query correctly
reports this attribution as UNKNOWN and did not run its conditional probe.

Success requires one of:

1. A borrowed typed certificate records the source cause/task, incoming relation
   and replay owner, created seed, and actually selected relation at the owning
   transition; a source-directed query follows that certificate through the
   same provider's Capture, own FreshUse maps, and exact A_F consumer relation,
   preserving alternatives and ordered Replay inputs; or
2. The proof lane establishes the first owner that cannot retain/discriminate
   this association and supplies a concrete falsifier.

Certificate absence or bounded-resource failure remains observationally
unavailable and must not change admission, propagation, inference, diagnostics
or publication. This is finite source/native progress only; no universal A/B
theorem or production gate closes.

## Two continuing lanes

Proof lane: one constructive proof producer continues R172 revision 2 from the
exact source/Replay callers. Prove certificate faithfulness for direct-source
and Replay invocations, multiple Origins/relations, and relevant failure/unwind
paths; apply the result to the same provider/consumer spine and original parent.
An exact obstruction is a useful result; occurrence equality or a successful
probe alone is not.

Implementation lane: Luna/high owns the smallest private inert certificate at
the actual seed-selection transition and a typed borrowed view through provider
Capture/maps/consumer. Derive every field from its owner. Do not use it to choose
or validate solver behavior. No public API or source-syntax change.

Prior evidence: R171 confirms source membership and one successful candidate
inference for the unchanged fixture; R172 proof rev2 has a CLEAN review and
establishes source facts plus static direct-seed existence while retracting
direct-drain attribution. R172's query/harness and handoff have exact-hash CLEAN
review; they expose unavailable attribution and the probe remains NOT_RUN.
R169/R70/R71/R165/R166/Replay and the original A/B/F1/FK1 gates remain OPEN.

## Frozen inputs and dependencies

- Unchanged fixture `tools/inference-playground/examples/r171-formal-name-forwarding.yu`,
  SHA-256 `cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f`.
- R171 source proof `notes/theory/2026-10-21-r171-forwarding-instance.md`,
  SHA-256 `d19b5ceb2c1ace95ce2cc49bdd6c35ef4bd4de223f07e181a472a037a35a133b`.
- R172 proof rev2 note SHA-256
  `885ca6ca2eba9937cd7bc81ffb6bd384e8fa96d17cc26392b76e7de4a9876488`;
  handoff SHA-256 `ef35a47437ba1477736f895de4168a8fa8e9f0c43511dd620c9f486891dba1d8`.
- R172 CLEAN query code `crates/yu-solver/src/shadow_apply.rs`, SHA-256
  `13ae8de60293b91e24659090649ff84002f5632a8909451d3f7bd8492b61bea5`;
  implementation handoff is in `tasks/agent-loop/inbox/20261021-r172-implementation.md`.
- Baseline owners: `lib.rs` SHA-256
  `c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985`,
  `candidate_context.rs` `d884c20a98140da2a737d65f61faa97491bd9a2af7870bf3f0ea7dd428e9ffeb`,
  `candidate_scheme.rs` `9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225`,
  and `shadow_apply.rs` as above.
- Active design authority: user-approved top-level inference principles
  `notes/design/2026-10-11-yulang-inference-top-level-principles.md` and
  `rules/design-authority.md`; the proposed certificate is private observational
  evidence only, not an algorithm/semantic decision.

Any baseline, source, fixture or authority change requires a sequential contract
revision and fresh review. Preserve three UNKNOWN legacy reservations and all
unrelated R152–R163 work.

## Revision 2: separate proof baseline from implementation candidate

The proof baseline remains immutable commit `7ec64a3788175913a2be46331cf0f64c6bd5b407`;
its original code-owner SHA-256 values are `lib.rs`
`c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985`,
`candidate_context.rs`
`d884c20a98140da2a737d65f61faa97491bd9a2af7870bf3f0ea7dd428e9ffeb`,
`candidate_scheme.rs`
`9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225`, and
`shadow_apply.rs`
`13ae8de60293b91e24659090649ff84002f5632a8909451d3f7bd8492b61bea5`.
Activation metadata is commit `9547edfc7`. Neither commit substitutes for the
other.

Proof revision 1 is limited to those original source bytes. Its author stopped
source reads after observing `candidate_context.rs` change from
`d884c20a…` to `f9590577…`; no conclusion applies to edited bytes. The frozen
note and handoff hashes are respectively
`6a3fa980486875d671b6b2593baee910f1966467c8dec6980a36f29f9e1cb012` and
`fe66540651d427f3b5ac32f63f82232898cdb7bf4e9d1e7cdea0a28c0825f887`.
This is a baseline-qualified obstruction, not proof closure or an independent
review.

The current Luna implementation candidate is separately identified by these
four owner hashes at the revision 2 review boundary:

```text
99dc39e970b35f2d06a900826bf686ee5a76795430a3e4167ac5c64184da6af6  crates/yu-solver/src/lib.rs
ac1375954d0d310bbeaaccb09625dc4701dd1c25a050a67f1f203d91e9456b06  crates/yu-solver/src/candidate_context.rs
9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225  crates/yu-solver/src/candidate_scheme.rs
13ae8de60293b91e24659090649ff84002f5632a8909451d3f7bd8492b61bea5  crates/yu-solver/src/shadow_apply.rs
```

These hashes identify an intermediate implementation candidate, not a new proof
baseline. After this delta review, Luna may continue edits under the existing
implementation lease; every proof or final-code review must instead consume its
own immutable manifest. The receipt is observational only and becomes visible
only after enqueue succeeds. It distinguishes incoming relation, Replay owner,
created seed, selected relation and exact Origin index. Selection, enqueue and
drain completion remain distinct; absent receipts stay unavailable, and no
certificate field may alter inference decisions.

The review boundary charged the full 240-second preparation, 1200-second proof
grant and 1500-second implementation grant because proof elapsed time was
UNKNOWN and both lane grants were issued. The 720-second aggregate review grant
was also issued; its elapsed time is UNKNOWN, so the full 720 seconds are
charged. Luna explicitly reallocates the unissued 300-second conditional probe
grant to one fresh independent final-candidate review. The final 240 seconds
remain for closeout. The ledger is 3660 charged + 300 final review reserved +
240 closeout reserved = 4200 seconds. Once the final-review grant is issued,
charge it in full. The probe is revoked for R173 and stays NOT_RUN. There is no
carryover, Astra remains zero, and all original parent gates remain OPEN.

## Revision 3: final-review resource reallocation

Luna primary explicitly adopts revision 3. The candidate frozen in
`tasks/agent-loop/inbox/20261021-r173-implementation.md` revision 4 is the exact
review target; its complete six-path manifest and fixture hash are recorded
there. The previous 720-second aggregate review grant remains fully charged
because elapsed time is UNKNOWN. The 300 seconds formerly reserved for a
conditional probe are reassigned to exactly one fresh independent review of
the final candidate. No compiler, test, evaluator, Yulang2 or inference probe is
authorized in this revision. Closeout remains 240 seconds.

The review must inspect receipt availability after enqueue and completion,
retention after frame removal, exact task/CauseId/source-fact authentication,
direct versus Replay selection, invocation multiplicity, rollback/index reuse,
failure and unwind paths, and absence of certificate-dependent solver decisions
or publication changes. It must also establish the same-provider Capture/maps
and forwarding consumer join, especially whether requiring the Apply relation
inside captured provider bounds is justified. The reviewer may validate an
existing candidate-specific argument but must not invent a missing proof and
self-certify it. On a material finding, retain the frozen candidate and report
the exact first obstruction; no repair grant is implied.

## Exact leases if activated

Luna may write only:

- `crates/yu-solver/src/lib.rs`
- `crates/yu-solver/src/candidate_context.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `tools/inference-playground/examples/r173_source_drain_attribution.rs`
- `notes/theory/2026-10-21-r173-source-drain-attribution.md`
- `tasks/agent-loop/inbox/20261021-r173-implementation.md`

Proof worker may write only:

- `notes/theory/2026-10-21-r173-source-drain-attribution-proof.md`
- `tasks/agent-loop/inbox/20261021-r173-proof.md`

No tests, broad builds, Yulang2/Y3 runtime, evaluator, external oracle, nested
CLI, network, background service, or unrelated source changes. The unchanged
R171 fixture stays read-only.

## Permissions, review and resources

Hard cap **4200 active seconds**: preparation/authority reconciliation 240;
proof 1200; Luna implementation 1500; aggregate reviews 720 (fully charged);
one final independent review 300; closeout 240. Astra 0, no descendants or
carryover. Revision 3 revokes the conditional probe allocation; it remains
NOT_RUN.

No compiler command, test, build, Yulang2/Y3 runtime, evaluator or inference
probe is authorized by revision 3. Any future probe requires a separately
funded and reviewed contract revision. An inference probe would not prove the
universal parent.

One fresh independent review is required for the frozen final code/harness/query
candidate. Proof rev1 remains baseline-only and unreviewed as a parent proof; its
result does not certify the candidate or close any theorem. Luna integrates
only CLEAN reviewed exact paths, after checking the full outbound range. The
reviewer does not grant leases or start workers. No writer may alter a frozen
review target.

Stop on ambiguous source or owner identity; certificate not tied to selected
seed; altered solver decision behavior; incomplete required joins; writer
conflict; changed dependency; exhausted budget; or user STOP. Preserve all
parent gates OPEN absent genuine proof closure.

## Integration outcome

Before/after evidence is the exact R172 status (`UNKNOWN`, no probe) versus a
reviewed source task → selected relation certificate → same provider/Capture/
maps → forwarding consumer association, or a specific owner obstruction.
Record requested and observed runtime models separately, current worker STOPPED
receipts, hashes and probe status in compact current state. The next dispatcher
consultation occurs at the first material counterexample/authority/lease change,
integration seam or sprint end.

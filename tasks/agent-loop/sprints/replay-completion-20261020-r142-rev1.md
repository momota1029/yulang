# Sprint R142 candidate — replay child completion ownership

Status: **CANDIDATE; no source or theory lease/resources granted yet.**
Revision 1. Branch `research/simple-sub-intrusion`; baseline
`503e5c78ce67a4616044ce981030e5e1bda5223c`. Luna is primary, sole authority
owner and Git integrator. The candidate follows dispatcher selection at the
R141 sprint boundary.

## Original parent and fixed outcome

Original parent: `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1` and the unchanged
computation-forwarding preservation claim in
`notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7.
Preserve one shared satisfying assignment, original current-formal identities
and whole Name arguments, arbitrary finite prefixes, repeated calls,
simultaneous receiving entries and independent foreign-continuation
obligations. R70 entry validity/fiber coverage, R71 required-fiber lineage,
R72/R73, Simple-sub A/B, inference/evaluator correspondence,
source/native correspondence and production remain OPEN. R50 remains NOT
ADOPTED. No accepted semantics or source domain changes.

Fixed measurable outcome: prove a constructor-derived **replay-child completion
ownership invariant** from operation creation through queue transfer, typed
drain, child return and terminal acknowledgement; then apply it to the exact
remaining R70 drain premise. A successful result must distinguish transfer
from completion and identify the unique lifetime and child index that owns each
right at every stage. Alternatively, produce a constructor-authentic
counterexample to that invariant. Missing/error paths must be classified by
their retained, aborted or returned ownership; do not assume whole rollback.
This sprint cannot close the original parent theorem or infer a solver bug from
a conditional frame.

## Required construction and falsifiers

Inspect the actual owners, not an imagined queue protocol:

- `candidate_context.rs`: replay operation creation/identity, ordered child
  construction, `queued` and `consumed` frontiers, `ReplayChildWait`, child
  transfer/completion, operation retirement/reclamation and `ReplayDriveOutcome`.
- `lib.rs`: work-item `replay_ack`, queue pop/dispatch, `TypedDrainFrame` ack
  vector and prepared/completed cursors, replay destination, terminal drain,
  return publication, transaction commit/rollback.
- `candidate_intrusion.rs`: settlement, generation/currentness and retained
  lifecycle effects that can delay or redirect a replay child.

State and prove a conservation relation over operation lifetime plus child
index. Keep distinct: child construction, queue transfer, active drain owner,
prepared acknowledgement, completed acknowledgement, operation retirement and
storage reclamation. Multiple stored references are not automatically multiple
completion rights. `ReplayDriveOutcome::Queued` denotes transfer, never
completion. Account for `Idle`, `Running` and `Ready` ownership and every return
stage that can retain an acknowledgement. A counterexample must follow an
actual constructor/control-flow path from valid source-produced state, not an
arbitrary struct assignment.

Falsifiers: a production constructor loses a completion right, gives two
consumers completion authority for one child, acknowledges one child twice,
returns a drain while retaining an undisclosed obligation, treats transfer as
completion, or reuses a retired operation identity while an old reference can
still act. Also falsify any invariant that excludes an authentic error or
transaction path without identifying its retained/aborted owner. Do not demand
full rollback where the implementation retains safe ownership.

Apply the result to `R70-DRAIN-1`: name exactly what the ownership invariant
settles and the residual premise for execution/consumption, entry validity,
fiber coverage, source qualification or independent continuation. Keep R70 and
R71's exact accepted-source and raw/canonical lineage limits intact. A proof of
local ownership is not a source/native reachability theorem or a production
gate.

## Authority and implementation boundary

This is a read-only proof/source audit. Initial implementation status is
**NO_SAFE_CODE_SLICE**: the dispatcher found no approved-behavior defect. If a
genuine constructor-authentic defect is established, stop and return to Luna for
a separate exact repair amendment before writing code. No synthetic demo,
observer, instrumentation, compiler/test/build command, semantic change,
expected-output edit, API change or production promotion is authorized here.

## Exact outputs and reviews

- Contract: `tasks/agent-loop/sprints/replay-completion-20261020-r142-rev1.md`
  (Luna; candidate then frozen contract).
- Theory: `notes/theory/2026-10-20-r142-replay-completion.md`
  (constructive invariant/counterexample and parent application).
- Proof handoff: `tasks/agent-loop/inbox/20261020-r142-proof.md`.
- Progress receipt: `notes/progress/2026-10-20-r142-closeout.md`.

Before activation, obtain fresh prospective spec/authority and compiler/source
reviews of this exact contract SHA and direct pin set. After the proof and parent
application are frozen, obtain fresh independent compiler/source and
spec/authority reviews of the complete snapshot. No reviewer may author the
proof. CLEAN reviews certify only this finite ownership result, not R70/R71,
Simple-sub, inference/evaluator or production.

## Resources and stop conditions

Hard cap: **1,800 active seconds**, no carryover, zero Astra. Allocate once:
preparation and direct pin validation 120; prospective reviews 120; constructive
proof 900; Luna complementary constructor/control-flow audit 240; final reviews
240; closeout 180. Unknown elapsed time is charged at the full reservation for
its lane; no reset or automatic renewal. Preserve two review slots and all
three legacy UNKNOWN assignments, the board quarantine and held R104 lease.
No producer child starts before prospective reviews and Luna activation.

Stop on a counterexample needing code/semantic authority, dependency drift,
missing or unowned constructor state, inability to distinguish child rights,
review findings outside the envelope, exhausted lane budget or user STOP. A
conditional invariant with an unproved constructor premise is UNFINISHED/OPEN.
Only Luna updates `current.json`, adjudicates, stages exact paths, commits and
pushes. Git needs no user permission.

## Frozen direct dependency manifest (baseline/live SHA-256)

```text
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf  tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md
648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7  notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md
25f6a370ae1aa2d7a623a8aa0eaede979248d85b8c03c894fbf8f7850775e8db  tasks/agent-loop/inbox/20261019-r70-proof.md
a6bd6aa1ab369f77b728014cd51693b11c5b3f97f85aab392d6488c8834ac1fb  tasks/agent-loop/sprints/raw-canonical-fiber-coverage-20261019-r71.md
620947cece53ca60a7f8a2388a398f53850b835c79afd546bfdcfd10349a876e  notes/theory/2026-10-19-r71-raw-canonical-fiber-coverage.md
b7bc24379472bf840d111c379cbbf000516265c350d4ba55d47ecd06bb3fe2c6  tasks/agent-loop/inbox/20261019-r71-proof.md
002b9d86e26cfda6fdf094ea4d161501849a7127d55c2d147d408a781b9fd28d  crates/yu-solver/src/candidate_context.rs
c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985  crates/yu-solver/src/lib.rs
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
```

All dependencies are pinned to the baseline Git tree and must match live bytes
before activation and at proof freeze. Any drift requires a sequential contract
revision and fresh prospective review.

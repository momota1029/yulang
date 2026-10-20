# Sprint R143 candidate — public replay publication barrier

Status: **CANDIDATE; no proof lease or resources granted.** Revision 1.
Branch `research/simple-sub-intrusion`; baseline
`784bcf78516c0e59e4adfceac6c42ab6a10a087a`. Luna is primary, authority owner
and sole Git integrator. This candidate follows the R142 closeout boundary.

## Parent, outcome and limits

The relevant parent remains `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1` and the
unchanged computation-forwarding preservation claim in
`notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7.
Preserve one shared satisfying assignment, original current-formal identities
and whole Name arguments, arbitrary finite prefixes, repeated calls,
simultaneous receiving entries and independent foreign-continuation
obligations. R70 entry validity/fiber coverage, R71 required-fiber lineage,
R72/R73, Simple-sub A/B, inference/evaluator correspondence, source/native
correspondence and production remain OPEN. R50 remains NOT ADOPTED. This
candidate does not depend on R135's brace-shape decision and cannot be reported
as expanded Yulang2 Web-demo coverage.

Fixed outcome: for the ordinary public `CandidateInference::solve(hir)` route,
establish the finite **successful-return replay publication barrier**:

- Every replay child whose lifetime survives at successful return has its
  completion acknowledged.
- No authoritative queue, typed-drain, restoration or retained-session owner
  can still require a child completion after a solved result is published.
- A failed attempt returns no solved publication and exposes no reusable
  mutable inference session.

Cancelled or aborted lifetimes remain distinct from completed children.
Historical records may remain stored after retirement when their lifetime is
no longer live. This theorem does not establish unconditional termination,
fairness, source/native correspondence, behavior outside the ordinary solve
route or the original R70 theorem. An unproved branch is UNFINISHED, never a
counterexample by omission.

R142's local completion-ownership result may be reused only as reviewed partial
evidence; its exact hashes and limitations are pinned below. It proves neither
the public route nor final publication. The essential new work is a
constructor/control-flow induction that every successful path crosses the
barrier and every error path aborts before publication.

## Required caller closure and falsifier

Start with the observed path:

`CandidateInference::solve` → `solve_mode(false,false)` →
`ConstraintBatch::collect_candidate_mode_scoped_v1(..., true, true, false,
false)` → `InferenceSession::try_new_candidate` → `run_candidate(self)` →
`execute` → `finish_candidate(self)`.

Prove the publication barrier across the actual intervening owners, including
SCC schedules, loose/expression/root source actions, Local restoration,
fresh/open-use routes, terminal typed drains, transaction cleanup and final
result construction. Reconcile R142's result with this public entry, and pin
any intervening constructor before using it. Showing that a child has one owner
is insufficient; successful completion must cross the return/publication
boundary.

Falsifier: a constructor-authentic ordinary public route returns `Ok` while a
still-live child has an unconsumed completion right, or a solved result is
published while cleanup can still mutate or invalidate that attempt. A failed
route returning `Err` after consuming its private session is abort, not
successful publication. Do not assume failed rollback restored reusable state.
Retained but retired historical records are not live obligations.

## Authority and review gates

Initial implementation status: **NO_SAFE_CODE_SLICE**. This is a read-only
proof/source audit. No code, tests, builds, compiler execution, observers,
instrumentation, semantic changes, expected-output edits or production
promotion are authorized. A constructor-authentic defect stops this packet and
returns to Luna for a separate exact repair amendment.

Exact outputs:

- Contract: `tasks/agent-loop/sprints/public-replay-publication-20261020-r143-rev1.md`.
- Theory: `notes/theory/2026-10-20-r143-public-replay-publication.md`.
- Proof handoff: `tasks/agent-loop/inbox/20261020-r143-proof.md`.
- Progress receipt: `notes/progress/2026-10-20-r143-closeout.md`.

Before activation, obtain fresh prospective spec/authority and compiler/source
reviews of this exact contract SHA and pin set. After proof and parent
application are frozen, obtain fresh independent compiler/source and
spec/authority reviews of the complete snapshot. No proof author may review its
own work. CLEAN reviews certify only the finite public-return result, not R70,
R71, Simple-sub, source/native correspondence, inference/evaluator or
production.

## Proposed resource envelope

Proposed hard cap: **1,800 active seconds**, zero Astra, no carryover:
preparation/direct pin validation 180; prospective reviews 120; constructive
proof 900; Luna complementary caller/control-flow audit 180; final reviews 240;
closeout 180. Unknown elapsed time is charged at the full lane reservation.
No automatic renewal. Preserve two independent review slots and all three
legacy UNKNOWN assignments, board quarantine and held R104 lease. No producer
starts before CLEAN prospective reviews, refreshed live-pin checks and Luna's
explicit activation.

Stop on dependency drift, additional unpinned constructor, a defect needing
repair authority, inability to distinguish surviving from aborted lifetimes,
exhausted resources or user STOP. Only Luna updates `current.json`, stages exact
paths, adjudicates, commits and pushes. Routine Git needs no separate user
permission.

## Frozen direct dependency manifest (baseline/live SHA-256)

```text
838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543  crates/yu-solver/src/shadow_apply.rs
c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985  crates/yu-solver/src/lib.rs
cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7  crates/yu-solver/src/candidate_source.rs
2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850  crates/yu-solver/src/candidate_scheme.rs
002b9d86e26cfda6fdf094ea4d161501849a7127d55c2d147d408a781b9fd28d  crates/yu-solver/src/candidate_context.rs
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
25f019b0d96d8fefe5a7332458226cada068b6d4a07462138c4b3634441b0fdd  tasks/agent-loop/sprints/replay-completion-20261020-r142-rev1.md
5f1715db8ccef8777f89d9b64e8625efead68974be53beb8f55a84a86a014a2c  notes/theory/2026-10-20-r142-replay-completion.md
cbaa0c7e79ca9c04b4325b8358ec17664deb51eb4dc620be0c7e242041b44c26  tasks/agent-loop/inbox/20261020-r142-proof.md
900fb928cd8f1960d90ec7d6fdaac503aebe38e12848f5429f35719f0e91b16e  notes/progress/2026-10-20-r142-closeout.md
4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf  tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md
648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7  notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
```

The manifest is frozen against the stated branch baseline and live bytes before
activation. Any new dependency requires sequential revision and fresh
prospective review.

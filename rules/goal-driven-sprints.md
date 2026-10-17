# Goal-driven sprint operating contract

Authority: [the 2026-10-16 user decision](../notes/design/2026-10-16-goal-driven-sprints.md).
Scope: authorized ongoing research/simple-sub-intrusion work only. Unchanged
semantic, proof, review, Git, question-board and testing rules remain binding.
This file is the single current scheduling contract; legacy cadence never wins
by being read later. Maintenance/status/plan-only requests do not activate work.

## 1. Fix a meaningful outcome before splitting work

Luna and `next_action_selector` agree one sprint ID and freeze its contract:
original parent claims/quantifiers/source domain, exact authority and baseline,
implementation goal, measurable success evidence, open premises with owners,
source constructors/consumers, dependency versions, non-goals, both lane plans,
exact output leases, review boundaries, resources and stop conditions.
Use `tasks/agent-loop/sprints/TEMPLATE.md`; the supplied Call/effects candidate
is a planning seed, not an issued assignment or a theorem claim.

Success concerns an original obligation closed/refuted, a genuinely smaller
remaining premise, a reviewed source/native path implemented end to end, a
major regression/invalid proof eliminated, or a shorter evidenced critical path.
Record before/after evidence and exclusions. Commit/note/test/consultation counts
are not success metrics. Auxiliary regression/performance work must name its
contribution to this sprint; it cannot indefinitely displace the parent goal.

A source-qualified counterexample can resolve the research question as REFUTED,
never as PROVED or as permission for dependent production. Revoke affected
prerequisite edges and quarantine dependent work while independent lanes continue.

The contract stays fixed across internal steps. A counterexample or authority
change may require a versioned contract revision approved by Luna; keep the old
claim and exact reason rather than silently narrowing it. Workers cannot revise
contracts, extend write paths, spend extra budget or invent production authority.

## 2. Productive lanes and autonomous continuation

Maintain proof and implementation lanes when independently useful, with stable
inputs and disjoint exact leases. A lane is a continuing responsibility, not a
claim that one process is always computing. No useful safe work means an honest
WAITING/BLOCKED state, never filler notes or fabricated RUNNING status.

Proof work targets the original obligation. A packet may contain a sequence of
related lemmas, construction, source audits and falsifiers. Apply each useful
lemma to its parent immediately; if a premise remains, name its owner and next
discriminating evidence. Internal candidate lemmas may support further research
within that same unpromoted candidate; they do not authorize production or become
reviewed theorems. A frozen coherent proof goes to fresh independent review.

Implementation uses already approved semantics and established prerequisites.
Prioritize an actual source -> constraints -> propagation -> consumer/execution
path. A packet may cover several related owner-local edits/checks. A genuinely
open A/B premise blocks only dependent production work. Minimal reversible
instrumentation/prototypes may supply source evidence only with an explicit
provisional boundary, falsifier and rollback/cleanup owner; keep cutover OPEN.

Within the fixed contract, budget, dependencies and exact leases, a worker may
finish a step and take its next related pre-authorized step without another
dispatcher round, review panel, new goal or commit. It may refine an internal
lemma/check not enumerated individually when it stays within those same bounds.
Uncertain authority, expanded leases or a new dependency returns to Luna before
writing. A frozen review target is immutable: continue on independent leased
outputs, or use a pinned immutable snapshot and invalidate review of changed bytes.

If one lane blocks, continue the independent lane. Refill from this sprint's
ready work, not an unrelated stream of micro-optimizations. At a milestone with
no implementation progress, inspect at least two relevant approved code owners
and either choose an end-to-end contribution or record NO_SAFE_CODE_SLICE with
owner-specific dependencies. Do not turn this audit into a per-test ritual.
After two materially different proof methods leave the exact premise unchanged,
change method/input/owner or seek a bounded core assignment; do not rename it.

## 3. Astra as a tightly bounded core producer

Luna remains primary. `implementer` stays pinned Luna/high, never silently Sol.
`prover` and `next_action_selector` normally inherit Sol/high. Astra is an
exceptional, tightly bounded resource for a named core mathematical risk, not a
default lane. Start with Sol/high or Luna's own construction. Assign Astra only
when the packet names a specific unresolved mathematical risk and explains why
the bounded specialist pass is useful. A prior Sol failure is not required.
Use medium effort, the actual spawn schema, and a frozen deliverable; do not
upgrade effort to compensate for an unclear claim or missing inputs.

An Astra packet can include F1 and related frame actions, FK1 as a distinct
quantifier, FIRST-RESULT-ADEQUACY, source constructor investigation and native
bridges when their real dependency graph belongs to the same parent goal.
Do not pretend one frame construction discharges unrelated foreign-continuation
quantifiers. Work through multiple meaningful stages, apply results to the
parent, and freeze a coherent deliverable or exact obstruction at the stop bound.

Default sprint envelope (tighten for the observed runtime and shared machine):
- at most 6 active/reserved/unknown agent assignments, within the existing global
  ceiling of 12 including coordinators/leaves; reserve 2 slots for review/integration;
- at most 1 Astra assignment at a time across astra_prover, native overrides,
  implementation_escalation and every subtree; default to zero Astra assignments.
  If the named risk warrants one, allow at most 1 assignment and 300 seconds of
  aggregate Astra active work per sprint, medium effort and at most 3 substantive
  stages. Count all descendants and escalation routes in this same total. No
  automatic renewal or per-stage reset; continue with Sol/Luna at the bound.
  Reserve and charge the entire grant when issued. If actual duration is UNKNOWN,
  or an interrupted/cancellation-pending descendant has no cessation receipt,
  do not return that unobserved time to the sprint budget.
- sprint active-work envelope 7200 seconds; each assignment has finite stages,
  wall time and checks; renew only at a material budget boundary, not per lemma;
- at most 4 known lightweight single-process probes and 1 heavy Cargo/build/test
  process, with one verification owner; default per-probe limit 1 CPU, 1 GiB,
  120 seconds, tightened when the environment requires it.

These are scheduling limits, not promises of background runtime enforcement.
The primary's available runtime/resource budget is always the stricter bound.
Unknown/cancellation-pending writers still consume slots and reserve their paths.
A failed launch consumes its attempt, not evidence of work. Capacity-only failures
get at most 3 identical attempts (initial plus 2); unsupported roles/parameters
fail immediately to a supported equivalent route. Rate/auth/permission errors
are not capacity errors, and never authorize model upgrades or limit bypasses.

Astra proof work never grants production-code rights. The separate
implementation_escalation role retains its Luna evidence and acknowledged
writer-handoff requirements and shares the same global Astra quota. Sol handles
complementary verification, adversarial searches and further proofs. A Sol worker
that helped construct a result cannot independently certify it; use a fresh
isolated compiler_referee/spec_auditor as required. Model capability is not authority.

## 4. Lightweight dispatcher and primary receipts

Consult `next_action_selector` at sprint start/end, a material proof obstruction
or counterexample, substantive authority/dependency/lease/resource change,
a cross-lane integration seam, or goal replanning. A routine result, test,
minor repair, review receipt, commit or internal successor is not by itself a
consultation trigger. Coalesce related events; do not interrupt safe work or
wait for both lanes just to schedule one seam. Safety cancellation is immediate;
record/consult afterward when feasible. STOP never waits for the dispatcher.

The dispatcher proposes the sprint and dependency/resource adjustments and may
originate useful work. It neither grants leases, starts workers, certifies
results, changes semantics nor performs Git. Luna validates proposals and grants
a continuation envelope once. Workers send compact frozen handoffs to Luna;
no compulsory dispatcher acknowledgement is inserted between internal steps.
Only Luna assigns fresh independent reviews and integrates accepted artifacts.

## 5. Small current state, immutable evidence and ownership

`tasks/agent-loop/current.json` is the sole mutable scheduling snapshot, owned by
Luna (or exactly one explicitly leased recorder). The dispatcher is read-only
by default and returns deltas. This supersedes its old board-file write lease
only after the old writer's acknowledged handoff. The small `board.md` links
current state and history; do not maintain another detailed mutable queue.

Keep current state <=16 KiB and at most 32 active/blocked/pending-review entries.
Retain only the active sprint, workers, requested/observed settings, live/frozen/
quarantined leases, ready next work, pending review/integration and history
locators. Archive resolved receipts in a uniquely named frozen sprint milestone,
verify its hash/reference, then remove only resolved entries from current state.
Do not discard active/unknown leases or unconsumed results to meet a size limit;
stop admissions and checkpoint/resolve them. No full historical-ledger startup read.

A worker owns only its exact artifact and handoff paths, including generated or
scratch outputs. Use one handoff file per multi-stage assignment, not per lemma.
The handoff contract in `tasks/agent-loop/README.md` carries original parent,
contract/dependency/artifact hashes, authors, claim class, evidence, missing
premises, next in-scope step, mutual TODOs and writer-stop status. Frozen inbox
ID/revision/hash intake is idempotent; a changed same-revision hash is a conflict.
The primary can acknowledge frozen submissions directly. Existing inbox history
is preserved; requests alone do not assign work or transfer a lease.

## 6. Runtime truth, STOP and resumption

Keep planned task state separate from observed worker state. ASSIGNED is not
RUNNING. RUNNING needs a current-session actual launch/resume acknowledgement,
worker ID and active-work receipt. A retained idle worker is WAITING. Requested
model/effort and effective observed model/effort are separate fields; absent
metadata is UNKNOWN. A successful request or configuration parse proves neither
execution nor a particular effective model. Record a known routing mismatch;
never call Sol a Luna implementation worker or claim Astra from a request string.

On STOP/pause/session end, request cancellation through supported runtime tools,
record returned evidence, and clear RUNNING observations. Without confirmed write
cessation use UNKNOWN and quarantine every relevant lease; do not falsely mark
STOPPED or release capacity. Confirmed stopped workers become STOPPED. Reconcile
all descendants before reclaiming a coordinator's subtree. A lease never expires
into safe ownership just because time passed, the board changed or a session ended.

On resume/restart, revalidate authority and dependency hashes, reconcile actual
worker identities and outstanding leases, and require fresh active-work receipts.
Do not copy RUNNING, reset spent sprint budgets, resurrect a cancelled assignment
or spawn duplicates. Unsupported spawning yields explicit degraded serial primary
work, not several fictional agents or independent self-review. No nested CLI,
polling daemon, automatic hot reload or post-session background work is implied.

## 7. Review, coherent integration and reporting

Freeze artifact bytes and direct dependencies for independent review. Batch
findings and use delta review under unchanged M0-M3 limits. All accepted blocking/
major findings must close before acceptance; a producer or coauthor is not a
reviewer of its own artifact. A test pass is not proof/source coverage. Preserve
separate mathematical, source/native, implementation and production gate statuses.
Unreviewed candidate results can be checkpointed only under the existing narrow
research-only fast path, never as closed gates or approved production policy.

Integrate at a substantial verified milestone or safe preservation checkpoint,
not automatically after each lemma/test. Do not defer all useful work until a
whole research program ends. Freeze only the integration dependency component;
other lanes continue. Recheck baseline/dependencies, exact paths, unknown writers,
pending questions and the complete outbound range. Only Luna commits/pushes;
never force-push or overwrite a moved remote HEAD. With connector-only access,
use a commit based on the inspected HEAD and a non-forced expected-SHA ref update;
preserve concurrent movement and reconcile/revalidate before any retry.

Before declaring a milestone complete, synchronize compact current state and a
durable outcome receipt with original obligations, before/after evidence,
implementation behavior, remaining premises, checks, review status, changed
paths and limitations. Link legacy task records when relevant rather than append
duplicate progress narratives. No record-only broad tests or extra review panel.

## One-time migration review gate

The checked-in migration snapshot records INDEPENDENT-REVIEW as NOT_RUN.
Before live adoption of this policy/tooling revision, Luna must obtain a fresh
isolated review of the frozen diff, adjudicate findings and record its receipt.
Keep the snapshot in RECONCILE until both that review and legacy-worker/lease
reconciliation finish. Static tests and the editing primary's reread do not lift
this gate. This is one adoption boundary, not a new per-step review ritual.

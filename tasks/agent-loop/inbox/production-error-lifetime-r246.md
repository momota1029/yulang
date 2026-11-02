# R246-PRODUCTION-ERROR-LIFETIME / handoff revision 1

Assignment-ID / revision: `R246-PRODUCTION-ERROR-LIFETIME` / 1.
Contract: `tasks/agent-loop/sprints/production-error-lifetime-r246.md`.
Contract SHA-256:
`e5319ef4faea4da5f57b39299e2557d1986b8bd2230d0392d6e85ee41bb10dd3`.
Baseline: `2c70049839210df7f12e3d3d68b17f1908ed897b`, independently observed
using read-only HEAD/ref files, no Git command.

Author/worker: `/root/sol_r246_error_lifetime`, constructive source prover leaf;
session `01a1873a-a93b-7dc3-a8ce-028a7b543a80`. Requested gpt-6.1-sol/high;
effective observed model/effort UNKNOWN. No descendants/coauthors/model switch.

Parent: unchanged full inference soundness/Rust goal, accepted source domain,
original Simple-sub A/B, shared witnesses and arbitrary independent satisfying
assignments. Exact edge `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1` /
`R70-ENTRY-WF-1`; lifetime question `R245-RETAINED-REF-1`.
**Parent delta zero; full WCurrent and parent OPEN.** No semantics or production
promotion. F1/FK1/foreign-continuation obligations are not identified or closed.

Exact leased outputs / all new paths:

- `notes/theory/2026-11-02-production-error-lifetime-r246.md`
- `tasks/agent-loop/inbox/production-error-lifetime-r246.md`

Frozen theory SHA-256:
`6ec2b144b1976eed7f3fe6e8a2a2ea65f9e23c1836980d288ae695f55a0a408a`.
Handoff hash is returned to Luna externally to avoid recursive self-hashing.
The theory note contains all 13 current dependency hashes and exact source
call sites. Final contract, all 13 pins and observed baseline MATCH.

Outcome: **candidate static source evidence / no production post-error
inference continuation / review pending**, not a Lean theorem, executed probe
or source-qualified counterexample. Exact informal result R246-EXIT is in the
note: every failed route transaction returns out of its owning production
session before later candidate_extrude/prepare_candidate_fresh_use/
freshen_candidate_graph_core. One branch first gathers immutable readbacks.
Lean declaration/theorem type/axiom dependencies NOT APPLICABLE; checker NOT RUN
under the no-Lean/no-build contract.

Actual result and application:

1. Five production transaction sites are exhaustively identified: route_internal
   (`lib.rs:18318`), route_incoming (`19242`), Local (`candidate_scheme.rs:5270`),
   operation-v1 CatchOperation (`candidate_effect.rs:1351`) and FieldBoundV1
   (`1461`). Begin/rollback/sampling failures remain availability errors.
2. Their actual consumers propagate errors through ordinary SCC execution,
   candidate graph plans or source schedules into execute, then consuming run
   or the actual public CandidateInference solve helper. run_candidate's body
   has the same consuming behavior; its actual callers found are test code.
   The public candidate path is separately traced rather than assumed to call it.
3. A real non-test exception to immediate error return exists in shadow_apply's
   readback solve path: DeferredSelectionUnavailable triggers immutable evidence
   queries and then return/disposal. The outer public inspection API can absorb
   the error as Ok(readbacks), after the session is discarded. This does not
   resume inference or reach later extrusion in that session.
4. Receiving-residual assembly is another actual non-test caller: its route and
   action calls propagate via `?`; failure leaves before the private session is
   moved into the returned experiment. Post-success publication failures also
   prevent escape of that experiment.
5. Both explicit RetainedResume transaction starts and injected Local
   pause/FailOne/retry consumers are cfg(test). Successful descriptor deferral
   and ordinary diagnostics are distinct from transaction availability Err.
6. Apply the result to R245 call+ (`lib.rs:14822`) and call- (`14835`): captured
   row/term/view/member/tail/payload/context/relation/scoped/replay/owner
   survivor obligations after failed transactions are **excluded for later
   extrusion because that continuation is absent**, not discharged by owner
   identity or rollback equations. Per contract no route-specific survivor
   equation is derived without a real continued extrusion path.

Remaining premise: successful-history producer/input validity and all other
R245 §3 WCurrent premises still need their source/proof owner. R71 raw-slot/
canonical-fiber coverage, queue execution and acknowledgement/settlement remain
independent. Readback consistency and arbitrary future private session callers
are not certified by R246-EXIT. No reachable post-error extrusion defect found;
implementation NO_SAFE_CODE_SLICE after inspecting actual route, Local, effect,
rollback/accounting and public consumer owners.

Prior work reused: R245's frozen native parameter equation, current constructor
inventory and conditional return at their existing premises. Rejected:
Err-alone reasoning, test retry as production reachability, successful lookup
as owner identity, rollback functions as survivor proof, and complete abnormal
restoration as a goal for discarded attempts.

Hash-gate history: initial declared baseline `64dcbc150aec64f7a17abb08171f4cea48c84ce8`
differed from observed `2c70049839210df7f12e3d3d68b17f1908ed897b`; source citation
paused until Luna corrected its admission-checkpoint baseline. The three extra
owner pins (candidate_effect/receiver/shadow_apply) were admitted by Luna and
rechecked before body citation. No lease, budget or semantic change.
All 24 historical R245 appendix records were also hashed: 23 MATCH; the mutable
R245 admission record drifted from `77bd3c3ea324caf3c6d4b876ce204f83e6086363e09bfe51b49a76b99a4d8fb4`
to `06da4c9da2cfde6ef33e3a49c71dd7b4bcd49a6b076d543ff2c81a76952bbeb9`.
Luna confirmed its administrative outcome/review append and excluded this one
record as a semantic dependency. Frozen R245 theory/handoff and all Rust pins
remain MATCH. It is not evidence for any source/proof/review claim here.

Checks/resources: static reads/searches, SHA-256, read-only baseline lookup and
output whitespace checks. Initial python lookup failed; python3 hashing worked.
No build/test/Lean/probe/Cargo, cache/scratch/generated output, production edit,
quarantined/runtime access, Git, external contact or descendants. Maximum 1800
active seconds, no renewal; precise active time/CPU/RSS UNKNOWN, reservation
retained. Clock observations 03:36:17 and 03:39:12 UTC on 2026-11-02 do not
establish complete active-time accounting.

Mutual TODO / next boundary: Luna assigns fresh independent compiler_referee
review of these frozen bytes, adjudicates, applies the accepted exclusion at
both R245 entry edges and retains named owners for the successful-history
premises/R71/acknowledgement. Falsifier: a non-test transaction Err is absorbed
while the same InferenceSession survives and reaches later candidate_extrude.
New callers require a fresh source-coverage check. Shared state and Git remain
Luna-only; producer is ineligible to certify its own result.

Worker state: **STOPPED / WRITES_STOPPED**, revision 1 of both outputs frozen
after final read-only checks. NO_DESCENDANTS; unresolved descendant leases NONE;
scratch/generated paths NONE. Only the two exact leased outputs were written.
No worker continuation is implied while review is pending.

# R143 ordinary public solve: finite replay publication barrier

Status: **CANDIDATE CONSTRUCTOR/CONTROL-FLOW PROOF; fresh review pending**.
This is a successful-return implication for the exact ordinary public route.
It does not establish termination, fairness, valid all-path inference entries,
required-fiber coverage, source/native correctness or production authority.
Author `/root/r140_action31_proof`, assignment R143-PROOF, session
`current-conversation-2026-10-20-r143`; no descendants. Luna supplied a
complementary source/control audit. Neither contributor independently certifies
the combined result. Requested Sol/high; observed effective model/effort UNKNOWN.

Contract revision1:
`tasks/agent-loop/sprints/public-replay-publication-20261020-r143-rev1.md`,
SHA-256 `e189a89f4a9974492ceb6999ff5c3d890aa5250882c014fb3a9f1c9608a7b5c5`.
Source baseline supplied by Luna: `784bcf78516c0e59e4adfceac6c42ab6a10a087a`;
activation commit supplied by Luna: `9d9a7d678`. The contract's candidate header
describes preparation; grants and CLEAN prospective reviews come from the
current-session activation receipt. This leaf performed no Git operation.
All 15 live input pins and the contract digest matched at entry and freeze;
baseline-tree validation belongs to Luna's activation receipt.

## 1. Claim and exact parent application

Fix the pinned implementation with `shadow-apply-candidate` enabled and one
ordinary `CandidateInference::solve(hir)` invocation. Consider a finite actual
execution returning `Ok(candidate)`. For every replay operation lifetime in
that attempt that survives cancellation/abortion, all its indexed children
have crossed terminal completion acknowledgement before publication. At the
return boundary there is no authoritative queued item, typed drain, active
restoration, Local continuation or mutable inference-session owner requiring
another replay-child completion. Retained retired history is allowed.

If this invocation returns Err, it returns no solved CandidateInference and
no reusable mutable InferenceSession. Failed rollback is not assumed to have
restored a reusable state. Cancelled/aborted children are not called completed.

This is an implication from a finite successful return, not a proof that the
invocation returns. `Ok` can carry solver diagnostics: no premise that its error
vector is empty is used. A nonreturning execution does not falsify this claim.
Other APIs, especially solve_scoped_experiment, solve_operation_v1_research,
test-only direct session finalization and retained synthetic resume adapters,
are not this entry. This selects the requested operation for analysis; it does
not narrow the accepted language or change ordinary inference.

The relevant parent is R70-DRAIN-1 under
R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1 and the unchanged computation-forwarding
preservation claim §§1,6–7 named by the frozen contract. The original shared
satisfying assignment, current-formal identities and whole Name arguments,
arbitrary finite prefixes, repeated calls, simultaneous receiving entries and
independent foreign-continuation obligations are unchanged. The new result
supplies the **ordinary-public successful-return** part of the drain premise;
it does not infer progress of an arbitrary private consumer or closure of R70.
R70 entry validity/fiber coverage, R71, R72/R73, Simple-sub A/B,
inference/evaluator, source/native and production remain OPEN. R50 remains
NOT ADOPTED. R135 and Yulang2 Web-demo breadth are unrelated to this result.

## 2. Public entry, initial state and publication path

The previously missing entry edge is explicit in `shadow_apply.rs`:

```text
CandidateInference::solve                         :270
 -> solve_mode(hir, false, false)                  :385
 -> collect_candidate_mode_scoped_v1(hir,true,true,false,false)
 -> InferenceSession::try_new_candidate(batch)     lib.rs:10217
 -> session.run_candidate()                       shadow_apply.rs:427
 -> execute()?; finish_candidate(self)            lib.rs:10446
 -> finish_observations(self)?                    :10453 / :17503
 -> CandidateSolvedResult { data: finished.data }  :10458
 -> Ok(CandidateInference { solved })              shadow_apply.rs:498
```

Ordinary solve therefore fixes scoped=false and operation_v1=false. Preflight
and collection may reject before a session is created; neither can publish an
inference session or replay operation. Collection retains source schedules and
recipes in a batch, not a mutable replay context. Immutable helper calls in
preflight/recipe checks do not receive the mutable InferenceSession and cannot
transfer a child completion right. No new HIR/SCC semantic theorem is assumed.

`try_new` allocates the session's empty worklist/diagnostic tables and live rows;
source-level/formal initialization assigns levels and allocates registration
entry rows, but admits no replay operation. `try_new_candidate` then calls
`start_candidate_graph` (scheme:1162), which publishes GraphState::default after
effect-state initialization/reservations. `State::initialize` (effect:299)
assigns its brand, not child work. Replay maps, typed drains, restorations,
Local use stack and route journal begin empty. Candidate graph effects are
true, so the legacy closed-finalization session is absent.

The ordinary path does not attach test-only support or a Local pause budget.
The scoped test observation block after run_candidate in solve_mode is guarded
by scoped=true and is inactive here. The public return follows the solved
wrapper without a subsequent solve step.

## 3. Boundary predicate and bounded reuse of R142

Write B for a session boundary satisfying:

1. typed_worklist is empty; context.typed_drains is empty;
2. every retained replay operation has c=children.len(), retired=true and
   wait=Idle, or has already been reclaimed;
3. every retained restoration is retired, with no active restoration step
   or replay-return barrier; no LocalUse cursor remains to restore a bound;
4. no source action owns a partially executed inner drain, and no active route
   transaction remains when a complete source action returns to its schedule.

A schedule itself can be active between actions; its Frame identifies the next
source action and is not an unacknowledged replay child. At full schedule return
the source frame is None. B does not require graph templates, relations,
evidence, fresh-use maps, retired historical records or source permissions to
be absent. It does not assert that every inference obligation is discharged,
nor require all dirty/semantic metadata to be zero.

Use R142's reviewed **partial private-path** evidence only for its actual
claims: a child right is identified by (operation lifetime,index), not only
RelationId; transfer differs from completion; popped acks stay in the frame;
terminal consumption is guarded by the exact consumed index; acknowledged
Running/Ready and restoration references delay reclamation; complete rollback
restores rights and removes cancelled lifetimes before numeric-ID reuse;
failed attempts follow a private consuming-session abortion path. R142 did
not prove this public entry or publication barrier. Its review did not prove
eventual progress, entry validity or required-fiber adequacy.

Here c=consumed and q=queued. Equal RelationIds at two child indices still
carry two rights. Multiple copies of one ack in current/frame/destination/wait/
undo are references with different control roles, not additional consumers.
An operation lifetime begins at its successful constructor and is not identified
with a later allocation reusing its numeric ID. Retirement, retained historical
storage and transaction undo do not themselves rename that lifetime. Rollback
removal cancels it; completed reclamation preserves its completion history.
The successful-return claim
includes completed/reclaimed lifetimes in the attempt's event history; dropping
session storage is never used to turn a pending child into a completed one.
Neither relation-currentness at intrusion.generation nor context's separate
lifecycle_generation is a child acknowledgement. No residual/provider/witness
lineage is identified by endpoint equality.

## 4. Exhaustive creation and successful-drain lemma

There are two ordinary replay-creation families in the pinned owners:

| Creation/driver | Dynamic owner and successful return |
| --- | --- |
| `candidate_replay_bound` (extrusion:867–909) -> begin_replay(...,false) -> drive_replay(...,None) | Called by candidate_apply_value/effect, extrusion's final allowance pass, context execution's registered-Allowance replay, or merge replay. These execute inside Context/Dispatch/settlement of the structured typed drain. Each completed call transfers every child; Queued is not completion. |
| `candidate_step_bound_restoration_child` (extrusion:801–865) -> begin_replay(...,true), linked to its restoration -> drive_replay(...,Some(...)) | Called by the synchronous restoration driver. Each completed replay must have consumed all children AND delivered the Ready barrier before the restoration advances. |

The compatibility begin_replay callback driver is cfg(test); it is not entered
by ordinary solve. The retained single-child adapter is used only by cfg(test)
resume helpers; ordinary restoration selects retain_child_step=false. The
shared numeric namespace also allocates restorations, which are not additional
replay operations with children.

Within a structured drain the asynchronous creation callers are exhaustive:

- lib.rs:12566/12579 calls candidate_extrude only from actual Value Dispatch;
  its selected-bound/source-link constructors do not start a source schedule.
- candidate_apply_value/effect are selected by apply_value/effect_task while
  candidate_graph is present; their replays stay inside that Dispatch.
- candidate_context_execute_relation (context:3575–3661) can replay a retained
  Allowance or apply its effect bound during Context, before Dispatch.
- settle_candidate_intrusion (intrusion:568–596), called at empty worklist
  from the typed drain, consumes pending parents. Its merges can replay all
  physical lowers (intrusion:701), adding work back to that same consumer.
- effect checking may enqueue ordinary ack=None tasks for Support/tails; these
  remain in that drain. Source metadata/term/annotation constructors can append
  ordinary bounds without creating ReplayOperations; they do not bypass an
  unconsumed child into publication.

This inventory is about the mutable inference owners, not a claim that every
admitted annotation is typed correctly. No new replay constructor or hidden
source-activation premise is inferred from a test.

**Transfer lemma.** A successful whole drive_replay(None) for a new nonempty
operation returns only after q=n. Its loop selects children[q], enqueue reserves
evidence/queue/undo before transfer, and transfer is followed by infallible
push. No-item with c<n returns Queued; it does not acknowledge. Empty operations
retire without a child. Errors after creation/partial transfer propagate; they
are not successful whole-drive returns. This is R70/R142's exact pinned
whole-drive property, rechecked at context:3931–4003 and lib.rs:12997–13022.

**Successful-drain lemma.** Suppose a structured typed drain is entered at an
idle source boundary (or as one synchronous restoration child) and returns
successfully in a finite execution. Every asynchronous replay born during
that drain has c=n before return; every item popped by it has its replay ack
consumed, if present. The drain restores the caller's processing slots and
removes its frame. A synchronous parent's remaining untransferred children
are outside this relative claim; its current child's ack is included.

Proof. `run_candidate_typed_drain` (lib.rs:12290) loops until step_typed_drain
returns Complete. Transport with current=None settles intrusion whenever the
worklist is empty; it then pops the front item or proceeds to Diagnostics only
when no item and no dirty continuation remain. New merge products are therefore
revisited before that transition. A current item is cleared only after Context/
Dispatch and all Function admission/enqueue steps finish. Function children
carry ack=None; raw-to-canonical requeues also carry ack=None. Neither steals
the original frame's retained ack. Context consumption and currentness skip
semantic work, not that frame obligation.

Every successful asynchronous producer in the dynamic interval has q=n by the
transfer lemma. By R142 conservation, an unconsumed child among [c,q) must
still have its authoritative queue/current/frame ack owner; it cannot hide in
a graph template or a newly started Local/source continuation. No such caller
is invoked from the inspected dispatch/context/settlement body. Thus queue
exhaustion plus current/Function completion accounts for all their transferred
items in the drain's ack vector. This argument allows more children to be
generated during processing; it assumes only the finite successful execution
under consideration, not a bound on how much work might be generated.

Diagnostics occurs before Acknowledgements. `candidate_replay_effect_conflicts`
walks conflict/dependency data and reports errors; complete_diagnostic_delta
settles diagnostic SCC/witness data; replay_witness calls report_incompatible /
report_solver_kind, which only retain error/provenance data. These phases do
not enqueue semantic tasks, create replay operations, or consume another
frame's ack. Their resource failures would prevent successful drain return.

The terminal owner (lib.rs:12730–12796) advances completed_acks only after
complete_replay_child succeeds for the exact child index. ReturnReady is
entered only after the entire ack vector is consumed. It publishes a required
Ready receipt before popping its frame, then restores prior processing. Hence
no unconsumed right for a replay born in this drain can remain at return.
On the final acknowledgement, acknowledge_replay marks the operation retired;
an asynchronous operation remains Idle throughout this interval. Its record
is either reclaimed or retained retired+Idle by transaction/restoration guards.
For a synchronous input, that child's completion and its Ready receipt have
both been produced; the caller still owns delivery of the receipt. ∎

This proof does not turn an observed empty queue into evidence of completion:
the transfer inventory and actual terminal phase are both necessary. It also
does not infer live child completion from the mere existence of a relation,
Replay dependency, physical admission or generation completion.

## 5. Restoration and complete owner-call lemmas

`candidate_begin_bound_restoration` saves opposite_count, original occurrence/
cause and the physical emission. It is called only with an idle worklist on
this path. `candidate_drive_bound_restoration` loops over the saved restoration
until a whole emission is returned; no finite successful return is inferred
from constructing its handle.

For an active replay, candidate_step_bound_restoration_child validates the
bidirectional restoration/replay references and calls drive_replay(Some(...)).
Idle starts only the next child with q=c; start_typed_drain transfers it and
the parent stores Running. The successful-drain lemma produces the exact
completion and Ready receipt. The parent's Ready branch clears wait to Idle
without a second acknowledgement. Only retired+Idle permits replay Complete;
only then does advance_restoration remove the handle and increment the saved
opposite index. If no child exists, the empty/exhausted replay retires without
inventing one. At next_opposite==opposite_count, the restoration retires and
returns its emission. Induction over the finite successful driver trace gives
that every replay created for its visited opposite slots is complete, with
no Running/Ready barrier left. Reclaimed records need not remain stored.

**Local.** `route_candidate_local` calls route_candidate_local_run with
pause_after=None. The owner captures/builds FreshUse before child restoration,
then retains one LocalUse frame. Each loop iteration pops that frame only
temporarily and pushes it back before any fallible step result escapes.
step_candidate_local_use advances next_bound only after the current restoration
returns; it begins the next bound only when none is active. After all graph
bounds, it admits/drains the root link and marks complete only after final
fallible publication storage preparation. A successful ordinary loop cannot
return Paused: it returns Complete only with this flag true.

The enclosing successful transaction commits replay state, then commit_local_use
moves the complete graph/row maps into LocalFreshRoute and pops LocalUse. The
published route retains relation/evidence/context maps, not a restoration or
ReplayChildAck cursor (scheme:168–199,656–691). Retained map data does not own
an unfinished child. Therefore a complete Local action from B returns B.
Before this point a partial frame/cursor remains an inner owner, so its mere
presence is not a successful Local return certificate.

**Module FreshUse.** freshen_candidate_graph_core (scheme:1536–1559) loops
over ALL captured graph.bounds. For each it begins a restoration and drives it
to successful emission before advancing. Its retained wrapper can return only
after this loop and checked retained accounting. instantiate_candidate_graph
then drains the fresh-root route before publishing FreshRoute. route_candidate_graph
resets scratch and propagates its result, not a retained partial restoration.
Thus a complete module FreshUse route from B returns B. No nominal equality
of original and fresh endpoints is needed for this ownership result.

**Open use.** route_candidate_open_use (scheme:1465) calls route_internal;
route_internal's transaction admits the exact ordinary route whose route()
consumer calls constrain_live_value before publishing routed-use ownership.
Successful typed return and commit give B. Incoming uses call route_incoming
and its graph-mode route_candidate_graph branch, already covered. All source
callers propagate an Err; no failed private route is resumed to produce Ok.

**Transactions.** A successful finish_route_transaction chooses the forward
state, takes route_journal, commits replay operations, publishes a complete
Local frame if any, clears workspace undo and leaves the spare journal inert.
Commit only retires/reclaims records already meeting their own guards; it does
not acknowledge children and is not used as a substitute for the loops above.
Since these complete owner calls have consumed their children before commit,
no mutable transaction owner remains requiring replay completion afterward.
Retired historical records and dormant bookkeeping storage are harmless to B.

## 6. Exhaustive source/SCC composition

The actual Action match in candidate_source.rs:1733–1768 is covered as follows.
Every row below is a successful-return fact from B; any early Err instead
selects §8's failure path. The table includes ordinary handlers even when a
particular input does not emit them.

| Action family | Returning owner / barrier argument |
| --- | --- |
| Fact | admit_collected_fact (lib:11246) admits then calls constrain_live_value/effect. CrossKind records diagnostics before semantic replay creation; other admission errors propagate. Successful semantic admission uses the drain lemma. |
| Link, ValueConstraint | admit_candidate_value_link (scheme:1989) calls constrain_live_value before returning. |
| Candidate Group/Apply | admit_candidate_fact (shadow_apply:1763–1924) completes slot0 Value drain before its Group effect slot1 or Apply effect slots1,2; each effect admission drains serially. Recipe checks/endpoint/term construction do not own pending child completion. |
| Lambda | admit_lambda_fact (lib:11322–11495) completely drains its selected slot3/slot4 effects before provider slot2, then drains that provider. Role-based omission of slot3 changes no consumer barrier. |
| FormalNameEffect | candidate_formal_effect_equal (effect:1436) drains both equality directions sequentially. |
| FormalEntry, FormalAnnotation | Entry permissions/row setup either create metadata only or call the formal equality drain; annotation admits/drains both actual Value links before retaining final domain/permissions. Source annotation construction is not itself an unconsumed ReplayOperation. |
| Ascription, Annotation, LocalAnnotation | candidate_annotation_pair / construct_candidate_local_annotation (effect:1551–1702) construct views/bounds, then call the actual Value/effect drains in sequence. PublishLocal installs only after construction returns. Its installation stores the local root/boundary and creates no child. |
| Install, PublishLocal | install_candidate_local_term (scheme:1971) stores metadata, not a capture/restoration driver. No replay constructor or queue transfer occurs. |
| Local | Complete Local lemma in §5; ordinary pause budget is None. |
| Module | Actual active-use test selects open-use transaction or incoming graph FreshUse transaction; both complete before Action returns. |
| Operation, CatchOperation | effect:902–1035 builds operation/signature state and calls actual Value/effect drains for its constraints. Catch's optional transaction commits only after inner success. No standalone un-driven replay creation occurs in these handlers. |
| FieldBoundV1 | operation_v1=false makes candidate_field_bound_v1_inner reject before child production if such an action were presented; that branch cannot witness ordinary Ok. Its separately enabled research API is outside the theorem. |

Direct signature-bound insertion is not silently assumed to replay immediately:
the producer census in §4 distinguishes storage from ReplayOperation creation.
Where a handler performs such construction, its later actual constrain calls
provide its returning drain. This theorem concerns actual generated children,
not proof that every required source/native lineage or propagation was generated.

`step_candidate_source` increments next only after execute_candidate_action
returns successfully. Its separate PublishLocal stage installs metadata before
advancing. drive_candidate_source loops to Complete(true); at that point the
source frame is None. The synchronous wrapper supplies Support::READY and
attaches no synthetic registration. A pause/suspension is not returned as
ordinary successful completion. Induction over completed source actions gives
B at each next-action boundary and B with source=None at schedule return.

Now cover BOTH execute paths, without guessing candidate_source.active:

1. If source_mode is false, execute first calls admit_all_collected_facts.
   That finite successful prepass serially handles every Candidate recipe,
   Lambda recipe and collected fact with the handlers above. It returns B.
   The candidate SCC plan's non-source branch processes internal open uses,
   captures/stages member graphs, publishes them, then handles incoming uses.
   Every open/incoming route returns B; capture/staging is graph/evidence
   construction, not replay-child transfer. Capture failure cannot become Ok.
2. If source_mode is true, the candidate SCC plan executes every member root
   source schedule before capturing/publishing any member graph. Each complete
   root returns B. This branch continues after member graph publication and
   skips the separate non-source incoming-use loop; Module source actions own
   their actual use routing. After the SCC plan, execute runs the loose schedule
   AND every expression schedule in order. Each returns B by the source lemma.

Empty component/action/expression sequences preserve B. Mixed source/fallback
collection may put fallback recipes into schedules; the Action proof already
covers them. Missing schedule/constructor checks produce Err, not skipped
successful child completion. No property of inferred endpoint equality is used
to establish this composition. All final store-accounting/resource calls after
these loops are non-producers of replay children. Thus a finite successful
execute returns with B and no source frame or active route journal.

## 7. Publication carries the derived barrier; it does not check it

run_candidate consumes the private session, first execute()?, then
finish_candidate(self). finish_observations builds occurrence projections and
counters, samples finish-output resources, takes error data, and moves
candidate_graph directly into FrozenInferenceData. Candidate mode's finalization
is None, so it does not take the legacy closed-arena finalization branch.
The function's ordinary remainder observes/moves metadata and storage; it
does not enqueue semantic work or invoke a restoration/typed-drain driver.

**There is no independent final replay/queue/drain assertion in publication.**
In particular finish_observations moves candidate_graph without checking every
stored operation's c/q/wait and drops worklist/session scratch fields rather
than serializing an active consumer. finish_candidate checks only its candidate
mode/closed-result conditions before returning CandidateSolvedResult. The proof
cannot infer B from those checks; B follows from §§4–6 before finalization.
A direct test call to finish_candidate without execute is not evidence of the
ordinary public theorem and is not licensed as a substitute barrier.

Since ordinary finish does not create a child, it preserves B's no-authoritative-
completion property while transferring the graph. A failed finish sample
returns Err while consuming the private session/result under construction;
there is no public solved value. On success CandidateSolvedResult contains
FrozenInferenceData, not a reusable mutable InferenceSession. shadow_apply's
ordinary wrapper then returns CandidateInference without another semantic step.

For contradiction, suppose ordinary public solve returned Ok while a surviving
child still required completion. That child was created either in a drain or
by restoration, by the exhaustive census. The complete execute call entails
that its enclosing drain/owner call completed. Sections 4–5 force its c=n and
any Running/Ready barrier delivered, contradicting the unconsumed right. No
post-execute producer can introduce a new child before the public return.
Likewise the source/Local/transaction composition leaves no hidden retained
session owner requiring a completion. This proves the finite public-return
barrier. It proves neither that the surviving evidence is source-adequate nor
that all such executions terminate. ∎

## 8. Failure, cancellation and absence of publication

Public preflight/collection/setup failures return Err before solved publication.
During execute, every handler/drain/restoration error propagates through its
source schedule or SCC route to run_candidate's execute()?. Local temporarily
popped frames are pushed back before the error result escapes. Transactions
attempt rollback; a complete rollback restores old rights and erases cancelled
lifetimes before numeric-ID reuse. A failed rollback may leave context reset
before workspace cleanup; R142's exact caller proof supplies non-dispatching
unwind and consuming-session abandonment, not a reusable-state theorem.

The public edge now completes that private error argument: solve_mode owns
session, calls its consuming run_candidate with map_err(...)?, and constructs
Self only afterward. An Err from execute/finalization therefore cannot expose
that session or a CandidateSolvedResult as a successful return. Post-error
accounting in route_incoming/Local can preserve or replace Err, but never
convert it into Ok and resume semantic work. Source wrapper cleanup only
clears its frame; SCC error cleanup only resets scratch/orchestration.

Compiler-reported incompatibilities that are retained in errors and allow
ordinary Ok still pass their normal drain/terminal consumers. They are not
availability-aborted lifetimes, nor evidence that every source typing or
hygiene requirement is correct. This preserves the distinction between a
diagnostic result, a cancelled transaction, an aborted attempt and a completed
replay child. No rollback-completeness requirement is added to language meaning.

## 9. Parent reduction, next work and mutual TODOs

Before R143, R142 supplied private-path completion ownership but left the public
entry and final publication implication open. R143 pins the actual public call
and supplies an exhaustive finite successful-return composition. The specific
remaining **public-return** premise in R70-DRAIN-1 is now supported by this
candidate proof, pending fresh independent review and Luna adjudication.

R70's entire theorem remains OPEN: valid actual entries, complete required
raw/canonical fiber lineage and any progress/termination premise outside this
conditional return theorem are not established. R71, the original parent and
independent foreign-continuation quantifiers remain OPEN. No change to ordinary
constraint generation, accumulation, propagation, levels, extrusion, qualifying
intrusion or generalization follows, and no withdrawn bypass is restored.

Mutual TODO `R143-PUBLIC-RETURN-REVIEW-1`: Luna assigns fresh compiler/source
and spec/authority review of this exact frozen snapshot and complete 15 pins.
Falsifier: an ordinary public successful path creates a replay outside §4's
census, returns from a listed owner before completing/delivering its children,
or publishes while an authoritative consumer remains. A test of assumed
transitions is not source constructor evidence. This is a request to Luna,
not a producer appointment of reviewers.

Mutual TODO `R70-RESIDUAL-ENTRY-FIBER-1`: apply the reviewed public-return
result only to the ordinary route; retain R70's exact entry/fiber premises and
R71's required-lineage owner. The next useful in-scope research step after
review is that actual missing constructor/consumer correspondence, not a
renamed general termination theorem. Any new dependency, observer or code
lease requires a new Luna envelope. No further stage runs after this freeze.

No source-authentic counterexample or approved-behavior defect was established:
**NO_SAFE_CODE_SLICE**. No provisional observer or implementation TODO is
required by this finite control-flow proof. Source/native and production gates
remain separate from its candidate mathematical/constructor result.

## 10. Provenance, input hashes, checks and resources

R142 author `/root/r140_action31_proof` and Luna's complementary source audit
are reused only within their reviewed partial scope; CLEAN review by fresh
`/root/r141_pre_compiler` and `/root/r141_pre_spec` certified that finite partial
research, not this theorem. R70 by `/root/r70_ordinary_extrusion_proof`, with
`/root/r70_extrusion_countertrace`, contributes its conditional extrusion and
successful whole-drive transfer facts, not entry validity/fiber closure. Luna's
R143 audit identified the public caller and unchecked publication seam; this
author independently read the pinned definitions and derived the composition.
Both contributors are ineligible to independently certify the combined result.

Rejected: transfer as completion, q=n as acknowledgement, c=n as immediate
reclamation, an empty queue alone as a barrier, direct finalization as evidence
for the public call, graph templates as active child owners, and R142's private
entry as already proving public activation. Historical failures/limitations
remain preserved in their actual premises.

The exact 15 direct live/baseline pins are:

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

Checks: static source/rule/proof reads, constructor/control-flow induction,
hash-only Python3 live-pin/contract validation, formatting inspection. No tests,
builds, compiler/solver execution, probes, observer, instrumentation, network,
Git, external contact, nested CLI or delegation. Source authorship is not
reassigned by this note. No extra proof dependency was imported.

Grant900 active seconds, zero Astra and no carryover. First explicit clock
2026-10-20 00:53:55 UTC. Actual stop interval and conservative charge are in
the frozen inbox/final hash receipt; CPU/RSS and provider-side active duration
UNKNOWN. All stages—entry, creator census, drain/restoration, source/SCC,
publication, failure and parent application—are complete as candidate proof.
Only this exact theory path and `tasks/agent-loop/inbox/20261020-r143-proof.md`
are new/written; no scratch paths or descendants. Both freeze for Luna intake,
then this writer stops. Fresh independent review/adjudication remain pending.

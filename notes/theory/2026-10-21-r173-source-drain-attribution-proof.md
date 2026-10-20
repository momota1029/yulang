# R173 source-drain attribution: exact owner obstruction

Status: **UNREVIEWED candidate construction lemma and source-owner obstruction.**
Assignment `R173-SOURCE-DRAIN-ATTRIBUTION-PROOF`, frozen result revision **1**.
Author `/root/r173_source_drain_proof`; no coauthors or descendants.
Requested Sol/high; observed model/effort **UNKNOWN/UNKNOWN**.
Baseline supplied by Luna: `7ec64a378`; no Git operation performed.
Luna's current-session activation after prospective CLEAN review grants this packet;
the pinned contract's prospective CANDIDATE header is not a runtime receipt.

## Dependency-change stop receipt

The initial SHA-256 check matched all contract pins. The final check at observed
2026-10-20 16:20:37 UTC found `candidate_context.rs` changed from expected
`d884c20a98140da2a737d65f61faa97491bd9a2af7870bf3f0ea7dd428e9ffeb` to
`f95905777e93a40fdc4208cc345c3c2fbb64990f0d79210743282f4423147b46`.
The other three source-owner hashes still matched. The worker did not make that edit.
Reads were not taken from a separately retained immutable source snapshot; source line
locators describe the baseline excerpts audited, not the changed file. Therefore this
packet is not a coherent frozen current-source correspondence proof. Source work stopped
immediately and the change was reported to Luna. Only this leased artifact and handoff
are completed to record the stop. No changed dependency is adopted. Luna must reconcile
writer ownership and approve any sequential contract/dependency revision before further work.
The owner-obstruction and conditional-construction analysis below remains a candidate
about the audited baseline excerpts, pending fresh independent review.

## 1. Parent and actual result

Parent: `2026-10-15-computation-forwarding-preservation.md` §§1,6–7,
SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`.
Preserve its shared satisfying assignment xi=(nu,K,D), original declarations/formals,
open incoming E, arbitrary finite chains without a fixed length bound, repeated calls,
simultaneous entries and every well-typed finite prefix, including raw resumptions and
ordinary handler/guard/value-arm cases with the parent's explicit base hypotheses.
R171's unchanged terminal/relay fixture is one finite member, not a domain restriction.
No independent F1/FK1/foreign-continuation quantifier is discharged here.

**Actual result:** the baseline lacks the requested retained source-task/selection
certificate. The first owner with all its operands simultaneously is
`lib::start_typed_drain:12272–12287`; it does not retain their association.
This packet establishes the construction-local selection equations below and identifies
phase, multiplicity and rollback requirements for a faithful observational certificate.
It does not prove that an unimplemented constructor emits that certificate.
Source fact → selected relation → same terminal Capture/own maps → exact A_F consumer
remains **UNKNOWN**. This is an evidence obstruction, not a source-qualified semantic
counterexample or a proof that every construction-directed recovery is impossible.

The method changes from R172's inverse occurrence matching to the forward owning
transition and its exact retained-output boundary. The unchanged parent is not replaced
by a renamed conditional theorem.

## 2. Selection lemma and its exact hypotheses

For one invocation write `(t,o,c,r,a)` for its entry operands: raw LiveConstraintTask,
full ConstraintOccurrenceId, CauseId, incoming optional RelationId and ReplayChildAck.
After a successful `candidate_context_seed_with_formal(t,o,...)` return, let s be the
returned optional relation and q the assigned `item.relation = r.or(s)`.

On the candidate-graph path a successful helper return gives s=Some(seed). The seed
is computed from `candidate_context_pair(task_pair(t))`, source context and source/scoped
payload. `relation_with_scoped:2975–3005` interns the complete RelationKey. The helper
appends Origin for the invocation; raw t and its canonical relation pair are distinct
evidence, neither replaceable by equality of endpoints after later changes.

| Actual constructor | Incoming operands | Selected q |
| --- | --- | --- |
| Authenticated direct source admission | r=None, a=None; exact source receipt/task established at its owner | s |
| Synchronous Replay child | r=Some(operation.children[i]), a=Some(operation id,i), t=operation.task | r |

Proof: these are the two Option::or cases applied to the actual callers. The Replay case
holds even if r=s by interning. Its newly created Origin does not prove seed selection.
The inherited o/c does not make operation.task the original source fact's task.
`candidate_context_step_replay_child:3912–3946` copies the operation's actual task, child
and acknowledgement before calling start_typed_drain. Running/Ready checks subsequently
compare the exact ack, index and drain destination. Ordered Replay inputs stay independent.

No-ack/no-relation alone is a disposition, not a universal source-origin criterion.
A direct-source label additionally requires its admission's cause→FactId→stored Terms
and the constructor-derived conversion of those Terms to t.
`ConstraintStore::admit_and_record_provenance:3671–3721` retains a successful source receipt;
Lambda callers at `lib.rs:11409–11424,11477–11487` construct their actual tasks with absent
r/a. R171/R172 supply the Name/body/Apply operands within their recorded premises.
No generic no-ack work item is relabeled as direct source.

**Conditional construction lemma:** a private row copying `(t,o,c,r,a,s,q)` from this
same invocation after successful selection faithfully records its selection, provided
it retains a construction identity distinguishing live equal-valued rows and only the
phase/history actually established in §3. Proof: copy t/o/c/r/a before mutation; s is
this call's successful helper return; q is the subsequent assignment. The two cases
above distinguish source and Replay without inverse identity inference. Construction
identity preserves separate invocations sharing values. This proves the copying
constructor's proposed meaning, not baseline emission, drain completion or consumer reach.

One row per occurrence/relation is insufficient: different Origins and invocations can
share those keys. A graph-owned row ordinal can distinguish retained events if no
rolled-back/reused ordinal is treated as stable across histories. This creates no
semantic runtime receiver identity.

## 3. Failure, unwind and lifetime boundaries

1. `begin_typed_drain:2184–2194` pushes a frame before diagnostic clearing, resource
   sampling and seeding. Those operations can fail; frame presence certifies no selection.
2. `candidate_context_seed:3340–3350` appends Origin **before** its fallible final
   `sample_f4_resources`. An Origin can therefore exist when the helper returns Err:
   no seed result reached start_typed_drain and `.or(seed)` did not execute. Inferring
   successful selection from such an Origin is unsound attribution.
3. After selection, `enqueue_item:12994–13019` still reserves worklist capacity and
   validates/transfers Replay ownership before insertion. Its fallback evidence branch
   only runs when relation=None; successful candidate seeding makes q Some, so enqueue
   preserves q. Reservation/transfer can still fail: selection is weaker than enqueue.
4. Enqueue is weaker than completion. Transport can replace the relation; context,
   dispatch, diagnostics and acknowledgement completion follow. Actual dependencies and
   current residual/scoped payload must carry the association through these stages.
5. `run_candidate_typed_drain:12290–12317` pops a newly created frame on error and restores
   previous processing. `candidate_context_consume_replay_child:3974–3997` truncates new
   Replay frames and clears waiting state on error. Neither alone establishes full state
   restoration or successful publication. The governing requirement remains necessary
   abnormal-path safety, not a new whole-route rollback obligation.
6. `candidate_step_typed_drain_terminal:12729–12791` completes acknowledgements, retains
   Replay Ready where appropriate, then pops the frame. Transient task/cause/ack pieces
   do not provide a durable selection association after terminal completion.
7. `candidate_context::State::checkpoint/rollback:1994–2113` restores/truncates frames, operations,
   relations, dependencies and Origins. A future sidecar must follow its owning history
   or make invalidated rows unavailable. A removed/reused relation, operation or event
   ordinal cannot authenticate a different later history.

A sufficient discipline for the conditional lemma is a borrowed context-owned observation
marked with the phase established, or a row exposed only after successful enqueue with
later failure/rollback invalidation. Completion claims require their actual owner evidence.
Optional observation retention failure must make evidence unavailable; it must not create
a solver rejection, change diagnostics, choose a typing or affect publication. In
particular a new sidecar allocation error cannot propagate into otherwise successful
inference. This is a provisional obligation, not producer approval of a storage design.

## 4. Application to the original terminal/Capture/maps/A_F spine

Reuse R171's source identities and R172 rev2's static direct-seed existence. Select
terminal L_T slots 2/4, N_T slots 1/2, distinct definition-final Link30; relay argument
N_R slots 1/2 and forwarding A_F slots 0/2. A_F's module callee resolves to D_T. No numeric
FactId, Term, route or q_F is inferred from a successful trace.

At each actual direct admission the new selection lemma says q=s once the missing owner
row is constructed and authenticated against that receipt/task. Replay invocations for
the same o/c remain separate rows with selected r and owner a; their unselected s must
not be substituted as that direct-source event. All legitimate alternatives remain.

The next transitions have actual suppliers, but the complete instance join remains open:

- `Capture::bound:1020–1066` reads a raw BoundKey cursor before interning endpoints and
  retains each distinct relation with source_bound and EvidenceSnapshot. Deduplication
  of endpoint/relation keys does not preserve invocation identity. Distinct authenticated
  event rows sharing a relation must remain separate association alternatives.
- `freshen_candidate_graph_core:1548–1566` prepares one FreshUse and drives every captured
  bound restoration. `begin_candidate_fresh_bound:1875–1922` uses that FreshUse's terms,
  context_use, context/scoped/evidence maps and records source_bound/mapped_relation in
  BoundAdmissionCause::FreshUse. These are positive own-map suppliers, not proof every
  required original source bound was captured and activated.
- R171's consumer audit fixes A_F's own NativeInterface demand and FunctionPort AE/RE
  decomposition. Authentication of q_F still requires its positive provider from this
  same terminal route/map and its negative Function from that exact demand. Current
  endpoint equality cannot establish that owner association.
- The baseline R172 query at `shadow_apply:1030–1078` traverses Replay when either input
  is reachable while returning both ordered inputs. That establishes incidence through
  one input, not justification of both. Keep lower/upper BoundKeys, all Derived/Transport/
  FunctionPort alternatives, actual payload and independent per-component gaps.

The query honestly returns attribution UNKNOWN and structured-Capture, structured-map
and consumer-join flags false (`shadow_apply:1131–1138`). Selection equations repair none
of these retained-output gaps. Self-pair factorizations, unchanged endpoints, raw fibers
and justified shared-anchor/Transport routes remain eligible; absent physical self-pairs
are not declared witness loss.

Applied immediately to parent §6: **if** the remaining actual map/admission/consumer joins
are established, its existing reviewed implication gives
`e_nR <= mu_T(e_tT) <= mu_T(e_nT) <= mu_T(e_RT) <= e_C <= e_AF`;
relay's original Name equality/body bound then gives its original template `e_tR <= e_RR`.
This is the parent's existing conditional application. The present result gives no new
native inequality or authenticated mu_T. Copied relay→answer, universal mapped admission,
dynamic received root/carrier/Name/read/Force, R169/R70/R71/R165/R166/Replay,
A/B/F1/FK1 and production remain OPEN. The Simple-sub generation, accumulation,
propagation, levels, extrusion, qualifying intrusion and generalization are preserved.

## 5. Minimal mutual TODOs and discriminating falsifiers

`R173-PROOF-IMPL-1`, owner Luna, parent §6 source-to-instance bridge: retain/expose the
smallest inert typed observation at start_typed_drain from actual incoming task/cause/
occurrence/relation/Replay ack, this call's successful seed return and selected q.
Authenticate direct-source labeling through its owning receipt/task, distinguish repeated
equal-valued rows and the established phase, and expose only valid owning-history
associations. Outputs stay within Luna's existing R173 leases after her adjudication
and review. This TODO grants no implementation/probe permission or independent approval.

Exact source-level falsifiers (not executed source counterexamples):

- An Origin appended before a failing final seed sample is exposed as selected although
  the seed helper never returned.
- A failure of worklist reservation or Replay transfer after selection is exposed as
  successful enqueue/completion.
- A Replay row with incoming Some(r)/Some(ack) is labeled direct or selected from its
  created s; the error persists when r=s by interning.
- Two equal-valued invocations are claimed to be one unique event, or an invalidated
  ordinal authenticates a later reused ordinal.
- Optional certificate retention failure changes inference or publication.

`R173-PROOF-IMPL-2`, owner Luna, depends on -1 and the coherent frozen query: join every
required source receipt through its actual selected row, all dependency alternatives,
same D_T route, raw Capture witness (or justified unchanged/shared-anchor route), own
FreshUse maps and exact A_F relation. Falsifier: a purported complete tuple substitutes
a sibling provider/map/demand, omits the other ordered Replay premise, or resolves an
unknown component by endpoint/occurrence equality alone. The conditional probe remains
NOT_RUN before those joins.

No further producer stage remains after this packet's exact owner-obstruction stop.
Luna owns intake, implementation decisions and fresh independent review. A producer or
coauthor cannot independently certify the result.

## 6. Frozen dependencies, reuse, checks and cessation

Direct SHA-256 pins:

```text
R173 contract rev1  e4e6b0a93b00b69ece7b08ccd8d655a4fe096e351c42996186c1fc650d9511d0
initial assignment  af8853d55c35ad44b07e4544efbbd0c3ff7dc13b7d32b4571dda54629bda4cd8
parent              d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79
R171 proof          d19b5ceb2c1ace95ce2cc49bdd6c35ef4bd4de223f07e181a472a037a35a133b
R172 proof rev2     885ca6ca2eba9937cd7bc81ffb6bd384e8fa96d17cc26392b76e7de4a9876488
R172 handoff rev2   ef35a47437ba1477736f895de4168a8fa8e9f0c43511dd620c9f486891dba1d8
unchanged fixture   cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f
lib.rs              c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985
candidate_context   d884c20a98140da2a737d65f61faa97491bd9a2af7870bf3f0ea7dd428e9ffeb
candidate_scheme    9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225
shadow_apply        13ae8de60293b91e24659090649ff84002f5632a8909451d3f7bd8492b61bea5
sprint rules        e50f5d4f79814c87af56e7dc34ddb6ab968abb523826c72ecdc40a8920397c0a
handoff README      1379059577f4469ed930c0fc130e5cd169401cf9188dfcbbc482b92b43daebbf
design authority    e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1
inference principles 7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81
```

Prior authors: R171 `/root/r171_forwarding_proof`, R172 `/root/r172_source_capture_proof`;
the parent records its historical independent reviews. Reuse is restricted to R171 source
membership/operands, R172 rev2's corrected provenance and static seed existence, and
parent §6's real mapped-admission premise. R172 rev1's occurrence-equality attribution is
rejected. Historical successful inference and enumeration completeness do not certify
source-task attribution. Prior proofs remain within their actual premises.

Checks: bounded static source/authority reads, forward caller/phase/rollback analysis and
SHA-256 validation. Zero tests/builds/probes/compiler executions/Git/network/external
contact/descendants. A first artifact-write command using unavailable `python` exited 127
without creating a file; `python3` writes only the two leases. No scratch/generated paths.
1200-second cap; exact launch-to-stop active time UNKNOWN, no extension/carryover claimed.
Stop conditions reached: exact owning transition lacks the retained association; final dependency hash changed.
Writer STOPPED after frozen revision 1; no background work or descendant leases.
Pending fresh independent review and Luna intake/integration; all parent gates stay OPEN.

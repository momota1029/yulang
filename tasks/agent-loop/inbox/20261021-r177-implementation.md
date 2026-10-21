# R177-LUNA — construction-order and resource analysis

Assignment: `R177-CONSTRUCTION-ANALYSIS`, revision 1. This handoff is owned by
Luna. Start only after CLEAN prospective review and activation. It is a
read-only source-analysis assignment; no compiler write lease is included.

Read the exact immutable inputs in the R177 contract and proof packet:
`/tmp/r177-inputs/baseline-7ec64a378/` and
`/tmp/r177-inputs/v6-plus-construction-owners/`, all 10 source hashes and modes
as listed there. Also read the frozen R175/R176 notes and handoffs and the
original parent theorem and fixture at their exact hashes.

Trace the concrete producer/consumer order across source bound emission and
checking registration, seed/use capture, authentic FreshUse admission,
physical restoration/readback, same-provider Apply, both ordered Replay inputs,
FunctionPort consumption, and execution or current/reused-pair discharge. Name
the actual construction owner and stable identity at each join. Inspect at
least two relevant source owners. Record rollback, retries, publication and
failed partial updates. Identify the earliest boundary that fails to carry the
necessary association, if any.

Assess resource erasure independently: layouts, vector capacities, allocation
requests, shared allocator pressure, Arc identity/refcount, rollback,
publication and unwind. Distinguish proven invariants from assumptions and
state a source-supported design only when its prerequisites are explicit.
Current code status is **NO_SAFE_CODE_SLICE**; do not manufacture an edit or
alter semantics/tests/fixtures. A future code slice needs a separate exact lease
and prospective review.

Grant: **600 seconds**. UNKNOWN elapsed charges the full grant. No tests,
builds, probes, Yulang2/evaluator execution, network, Git operations or scratch
outputs. Write only this handoff. Report concrete owner paths, dependency hashes,
evidence, exact blocker/possible slice, omissions, budget and writer-stop state.

## Frozen Luna analysis result

Outcome: **NO_SAFE_CODE_SLICE**. This is a source-path analysis result, not a
claim that the original theorem or candidate implementation is complete.

The immutable inputs were verified at activation: ten files in each snapshot,
each file `0444`, each root `0555`; new-owner hashes match in baseline and v6:
`candidate_source.rs` `cbc39315…1065f7`, `candidate_call.rs`
`e038ad0d…80d479`, and `candidate_intrusion.rs` `475edf15…3cccd97`. Contract
SHA-256 is `4ee68f0106d9aa9dbf57f8de273a6d4554935726183118d22520fcd639667eac`;
proof packet SHA-256 is `df05f94d0c8b35d12fdb1df3a2f8e850bf8632af9a78294ffc60e41fd2c7f047`.
The proof worker independently confirmed the input manifest and pins before
reading source.

### Source emission and registration

`candidate_source.rs::emit_candidate_source` (`:827–849`) checks the exact
`LocalSource` object against the HIR owner, validates the Definition/Expression
parent and occurrence ownership, records occurrence-to-source-root entries,
and retains the source carrier. It builds formal/name side records
(`:855–934`) and, at Apply construction (`:1388–1427`), retains an
`ApplySourceInput` with exact source owner, expression, callee, argument,
checking occurrence/cause, endpoints and recipe index. This establishes a
source-keyed observation carrier for the collected Apply.

It does not establish that every original Name/body inequality is registered
as the exact checking fact later selected by capture. The source-reference
graph's registration producer is outside the ten reviewed files; the proof
worker independently identified `candidate_value_graph.rs` as an unpinned
owner at the first source-to-checking-registration seam. No read of that owner
or lease expansion occurred. A per-expression owner entry and Apply source
record do not by themselves prove universal source-bound coverage.

### Apply observation versus consumer construction

`candidate_call.rs::observe_inner` (`:490–660`) authenticates the retained Apply
against its exact HIR source owner, expression, callee/argument, checking
occurrence and `CauseId`; it verifies source scopes and the shape/polarities of
the retained native ports. `observe_scoped` additionally authenticates a
restricted Local-callee route (`:691–750`). These checks establish faithful
observation of an admitted candidate source call.

The returned `CandidateSourceCall` still exposes a
`PendingCallConstruction`: its `OriginalGenCall0Input` list is an inventory,
and `suppliers()` lists unsupplied original registration/interface,
introduction, checking/seed exposure, GenCall0, argument reification, receiver,
and module-use correspondences (`candidate_call.rs:243–277,380–427`). Its
`unresolved()` returns `shadow_apply::UNRESOLVED`. These source APIs request
construction evidence; they do not show that the actual provider Apply has
been formed from all required inputs or joined to both ordered Replay parents.

### Current/reused pair marker

The newly admitted owner `candidate_intrusion.rs::mark_candidate_pair`
(`:423–455`) saves and writes `completed[processing_relation] = generation`
when the admitted typed pair is its canonical pair. `lib.rs::record_typed_pair_admission`
calls it before the pair is inserted/replaced and before the value/effect task
is applied (`:13098–13170`). Later `pair_is_current` (`:11593–11603`) uses
presence of that pair and the relation-generation marker to suppress duplicate
work; the Value path returns at `:12517–12522` before decomposing a Function
pair. Rollback restores the prior completion entry (`candidate_intrusion.rs
:201–244`).

This is a generation-scoped work/deduplication marker with rollback support. Its
key carries a relation and generation, not four child FunctionPorts or evidence
that all four were consumed and discharged. Thus it cannot presently serve as
the missing source-to-current/reused-pair consumer certificate. The earlier
R176 concern is narrowed to this explicit writer and use, but the authentic
consumer-discharge relation remains OPEN; this analysis does not declare a
runtime or soundness bug.

The function branch makes the temporal gap concrete: after
`record_typed_pair_admission`, it stores all four `(FunctionField, TypedPairKey)`
children and enters `FunctionAdmission` (`lib.rs:12685–12725`). Later
`candidate_step_function_dispatch` obtains a per-field relation through
`candidate_function_port_admit`, stores a pending typed-work item and advances to
`FunctionEnqueue` (`:12835–12861`). Therefore the generation marker is written
before the parent drain has admitted/enqueued its four child ports. A sufficient
reuse argument would need a separate invariant relating the typed-pair entry to
each port's pending or discharged state, including rollback and rewrites; this
snapshot does not supply that relation merely from the marker.

### Resource boundary and handoff to proof

The snapshot-backed resource accounting in the owners includes retained source
input capacity (`candidate_call.rs::State::bytes`, `:146–165`) and candidate
intrusion state bytes (`candidate_intrusion.rs::State::bytes`, `:251–269`),
including the `completed` table. This census does not prove equivalence with
the baseline's allocation requests/capacities or shared allocator state.
`Undo::bytes` accounts its completion journal's owned capacity (`:278–289`),
and rollback restores completion values, but neither establishes no optional
allocation pressure, equal field layout, Arc/refcount headroom or unwind
noninterference. Resource erasure stays OPEN.

Mutual TODO for `/root/r177_source_consumer_proof`: apply the source-registration
gap and pending Call/consumer seam to the original parent; classify whether
`candidate_value_graph.rs` is the earliest missing constructor; preserve the
consumer marker limitation and resource OPEN premises. The proof worker has
not yet frozen its artifact at this handoff.

No code write, test, build, probe, Yulang2/evaluator execution, Git, network or
scratch output occurred. No semantic, fixture or expected-output change.
Requested Luna/high; effective runtime settings and exact elapsed time are
unavailable, so charge the full **600 seconds**. **Luna source analysis stopped;
proof worker remains RUNNING under its separate lease.** All parent/A/B,
source-native, implementation and production gates remain OPEN.

## Handoff revision 2 — independent review receipt

Revision 1 of this handoff was frozen at SHA-256
`fbf8f499208ff4ee1027feecead0be7bb36833e73b9c30572d7ce6814bf057b3` and is
preserved at `/tmp/r177-state/implementation-result-r1.md` (mode `0444`). This
revision adds only the following independent review and proof-stop receipt.

Fresh independent reviewer `/root/r177_final_review`, role
`compiler_referee`, returned **CLEAN for the contracted unfinished-research
outcome**. The reviewer verified all supplied artifact and source hashes/modes,
and independently confirmed:

- source Name/Lambda emission supports only the scoped template application;
- the uninspected first registration owner is
  `candidate_value_graph::Graph::retain_source`, called by
  `candidate_source.rs:849`; absence from this snapshot proves no code defect;
- `CandidateCall` exposes a pending input/supplier inventory, not the original
  GenCall0/provider/consumer construction;
- `mark_candidate_pair` is written during admission before FunctionPort
  admission/enqueue and cannot certify four-port semantic discharge;
- successful local visitation follows the queued/pending/ReturnReady control
  flow, but canonical/rewrite/reuse visitation does not alone prove semantic
  discharge for the original parent;
- resource and unwind claims remain conditional and OPEN.

Reviewed proof handoff: `tasks/agent-loop/inbox/20261021-r177-proof.md` revision 2,
SHA-256 `fabfe39930de7cc2d36a18527b498e24194b40efd14efefb1f9b1479b776e4d9`.
Proof note SHA-256
`108480f5a5e9010ace53957d5b53d4b3e7ea44185dd870e3a99eebf4bfb9c81a`.
Contract SHA-256
`4ee68f0106d9aa9dbf57f8de273a6d4554935726183118d22520fcd639667eac`.
Frozen current-state review snapshot SHA-256
`049ae83e0fc5845db15044b7bfe4d836881034a3f619f32ab37c4468bebbf43c`.
Final review consumed **360 seconds**; elapsed/runtime telemetry UNKNOWN;
reviewer STOPPED with no edits, tests, builds, probes, Git, network, scratch or
descendants. Proof author `/root/r177_source_consumer_proof` is also STOPPED;
its handoff revision 2 and note are frozen at the hashes above, full 1200s
charged. Luna analysis is STOPPED, full 600s charged.

**Result:** R177 `CLOSED_UNFINISHED_RESEARCH`. The reviewed scoped result
identifies source owners and separates candidate visitation from consumer
discharge. It closes no original theorem, A/B, source/native, implementation or
production gate. Next dispatcher selection belongs to Luna.

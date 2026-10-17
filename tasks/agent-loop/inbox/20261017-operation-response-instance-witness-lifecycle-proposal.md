# Frozen assignment handoff

Sprint-ID: `operation-default-and-instance-lifecycle-20261017`.
Contract revision 2 / SHA-256:
`ed45bd2b259173a09897b7121e00fd7000a29286024571606edbfa631ce40f50`.
Assignment-ID: `OPERATION-RESPONSE-INSTANCE-WITNESS-LIFECYCLE-20261017`.
Handoff revision: 1; frozen bytes, pending independent review and Luna intake.

## Assignment and parent

Role / actual worker: Luna/high / `/root` primary.
Requested model and effort: gpt-6.1-sol / high. Observed runtime identity:
primary `/root`; effective runtime model metadata is UNKNOWN.
Exact leases:

- `notes/design/2026-10-17-operation-response-instance-witness-lifecycle-proposal.md`
- `tasks/agent-loop/inbox/20261017-operation-response-instance-witness-lifecycle-proposal.md`

Original parent: FORWARD-FIRST-CALL A/B, F1/FK1, `M_exit`, source/native and
production; all remain OPEN. Parent quantifiers and source domain are unchanged.
Luna began this lane only after the proof writer's STOP receipt. That output is
not a premise of the lifecycle equations below; the design relies on contract
rev2's pinned candidate proposal, prior source/native map and actual pinned
constructor/consumer files.

## Result and source/native evidence

Outcome class: unadopted design proposal / source-native correspondence map.
No semantic rule adoption, accepted-source proof, compiler edit, execution,
theorem closure or production authority.

The proposal names `StaticUseKey=(source_root, operation-expression occurrence,
SourceOperationId)` and `DynamicEventKey=(StaticUseKey,fresh request event)`. It
uses only existing constructor fields and makes the cross-phase identity
assertion itself an open obligation. It keeps declaration, static use, dynamic
event, response B and suffix answer A_S distinct. A Catch operation pattern is
a declaration selector; its action occurrence is the arm body, so the dynamic
request must carry its own use/event key to the consumer.

Source inspection found:

- HIR declaration identity contains family plus declaration `SourceNodeKey`,
  with distinct signature/name positions.
- Candidate `Action::Operation` contains declaration, owner, operation
  expression occurrence, target and level. `candidate_operation` builds
  temporary value/effect/view maps and slot 42, then drops those maps.
- `Action::CatchOperation` carries a different arm-body occurrence and optional
  payload/continuation endpoints. `candidate_catch_operation` builds separate
  maps; continuation response ports 62/63 and effect links 64/65 remain distinct.
  Exact Unit payload patterns have no payload variable and no slots 60/61.
- Runtime request state retains declaration, actual `SourceSite`, fresh event,
  observations and suffix. Captured `ResumeTemplate` retains nodes/root,
  declaration and original event, but not a source operation-use key or solver
  map. Capture validates/builds locally and publishes after materialization
  checks.
- The fixed Function-response specimen refuses before capture/pop. It does not
  demonstrate a successful continuation witness through resume.

The proposed `OperationUseWitness` contains only a `PartialConstructionTrace`
of exact generated map entries/origins. It is not a semantic `θ`, complete B,
`D_B/P_B`, admission, challenge observation, future family or current grant.
No direct candidate-map-to-runtime-consumer edge is established. The exact
source/runtime identity adapter, complete semantic transport and current runtime
resource bound remain OPEN.

Validation and lifecycle outline: exact source-root/occurrence/declaration
checks at each boundary; stage before publication; preserve one event per
dynamic request; keep old event identity historical on resume; fail closed on
stale/foreign/missing witness. Candidate storage would use existing checked
`Plan::bytes`, scratch accounting and `sample_f4_resources` seams; owner
verification must tie any rollback requirement to an invariant or continued
reuse that needs it. Runtime template storage currently exposes no byte/event
limit in the pinned path; a future code lease must add checked accounting and
atomic externally visible publication. Failed private attempts may be safely
terminated or discarded instead of rolled back when they cannot continue
soundly. No current code change is selected.

## Open premises and falsifiers

- `OPRESP-DEFAULT-1` / `OPRESP-ENTRY-1`: select the governing omitted-row and
  complete entry rules; C-OMIT remains unadopted.
- `OPRESP-DOMAIN-1`: map all original response tuples, providers, worlds,
  challenges, observations and futures in both directions.
- `OPRESP-CONTEXT-1`: construct actual ApplyOne typing, current world and the
  complete registered carrier.
- `OPRESP-NATIVE-1`: establish source-to-runtime use identity and producer to
  consumer transport without importing a different solver instance.
- Later reviewed design must settle retained storage bounds, state owners,
  runtime failure behavior and integration contract. Rollback is required only
  for an identified invariant or intended reuse; external publication remains
  atomic.

Falsifiers include merging distinct static uses by declaration/endpoint,
reusing one event across repeated requests, selecting an instance from a Catch
arm rather than the actual request, restoring historic eligibility, changing B
into A_S, inventing missing `θ`/future fields, or publishing after failed
validation/resource admission.

## Dependencies, checks and resources

Exact source dependencies are the 24 direct pins in contract rev2. They were
verified before relying on each lane; Luna inspected the pinned source/native
owners for this proposal. The prior proof output only supplied the sequential
STOP boundary and did not supply a premise to the lifecycle construction. No
dependency or authority was added by this design lane.

Checks were static source/design reads and byte-hash recording only. No tests,
fixtures, builds, compiler or runtime execution, probes, network or Git were
run. No scratch or generated files were created. Implementation-lane elapsed
time was not measured; charge the full 240-second cap conservatively.

Revision 3 acknowledges and repairs one major finding from the independent
compiler review: preserve atomic externally visible publication; permit safe
termination/discard of an affected private inference or machine attempt; require
rollback only where an identified owner invariant or intended continued reuse
needs it. No new dependency, semantic claim, default decision or code authority
was added. The proof artifact is unchanged.

STOPPED: both leased outputs are frozen; no descendants or background work.
No code is authorized. Fresh independent compiler delta review, spec review and
architect review must run sequentially against the revision-3 output hashes. The proof author is
not an independent reviewer of either combined artifact. Luna alone adjudicates
review findings, updates compact state and stages/commits/pushes explicit paths.

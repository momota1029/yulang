# R174: rollback noninterference and the ordered forwarding bridge

Status: **candidate mathematics and source evidence; incomplete native bridge**.
No independent review or parent closure. Author: `/root/r174_prover`, requested
configured Sol/high, observed model/effort UNKNOWN. No descendants. Final source
target is Luna's immutable R174 **v6**, not the mutable checkout.

## 1. Unchanged parent and application

Parent: `2026-10-15-computation-forwarding-preservation.md` §§1,6–7, SHA-256
`d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`.
Keep its shared satisfying assignment xi=(nu,K,D), open incoming E, original
formal/provider identities, finite resolved annotations, arbitrary finite
forwarding chains, repeated calls, simultaneous entries, and every finite typed
execution prefix. Pending computation, raw resumption, handler matching/guards,
value-arm suffixes and source-directed abandonment retain their original cases.
The R171 fixture is a witness, not the universal source domain. No independent
F1/FK1 or foreign-continuation obligation is discharged by a drain action here.

Reuse the reviewed source preservation theorem and original-template lemma
within their actual premises. For each actual provider use i, native forwarding
still requires one authentic map mu_i and actual admission of

```text
mu_i(e_t) <= mu_i(e_n) <= mu_i(e_R), mu_i(e_n) <= mu_i(e_t),
e_A <= mu_i(e_t), mu_i(e_R) <= e_C <= e_out.
```

The results below remove the particular stale-Origin completion obstruction
from the v6 logical completion path and identify real map/transport suppliers.
They do not supply original Name/body capture coverage, physical restoration or
per-use forwarding Apply joins. Thus the parent's native chain induction still
cannot consume its full premise. Dynamic receiving-view/read/Force/control
correspondence remains separately OPEN. No successful fixture, conditional
implication or retained record closes those requirements.

## 2. R173 obstruction and exact v6 repair application

R173 `candidate_context.rs:88–99` makes SourceDrainReceipt Clone, not Copy;
`prepare_typed_drain_update:2229` moves its Option out of a borrowed frame. This
is a static ownership obstruction, not an observed compilation result. The
following R173 trace describes intended branch behavior, not execution of those
uncompilable bytes.

For a frame and Origin both predating checkpoint C, let r have completed=false.
R173 terminal completion (`lib.rs:12820–12828`) removes the frame and replaces
Origin(r) by Origin(r+), with completed=true. State::rollback restores frames
through typed_drain_undo but only truncates Origins. Therefore:

```text
C: F(r), Origin(r)
 -> complete: no F, Origin(r+)
 -> later failure -> rollback C: F(r), Origin(r+)
 -> retry terminal: receipt equality fails -> IdentityExhausted.
```

This is a state-level rollback obstruction with an explicit pre-existing-frame
premise. Source reachability of that exact checkpoint is not newly proved here.
Origins created after C are truncated and do not establish this counterexample.
The R173 review's falsifier is reused as a locator, not independent certification.

V6 `record_source_drain_completion` (`candidate_context.rs:2150–2162`) appends
r+ to a separate event vector if try_reserve succeeds, otherwise returns without
a solver error. Checkpoint records vector length L (`:2035`); rollback truncates
to L (`:2050`). Terminal (`lib.rs:12820–12826`) calls the logger before popping
the frame and no longer changes Origin or checks its completion bit.

**Completion-frontier lemma.** Given the actual append/truncate operations and
ordinary completion of their clones, the event log after rollback C is exactly
its prefix at C. Proof: successful log calls append only; unsuccessful reserve
calls leave the log unchanged; truncate(L) removes every appended suffix event.
In particular the r+ from the aborted completion is absent. Restored F(r) can
complete again without the old equality failure, because that failure branch
has been removed. The Origin stays unchanged throughout. Repeating this argument
handles any finite sequence of such attempts and nested valid checkpoints.
This discharges the **specific stale-Origin completion/retry subpremise** of
R174-NI at v6, not all failure/retry/allocator/publication properties.

Event lookup compares the whole receipt: origin_index, source cause, task,
created/selected relation, incoming relation, replay acknowledgement and drain
index, with completed=true. Stack index alone is not identity. A fresh drain
appends a new Origin; rolled-back newly created Origins and completion suffixes
are removed together. These facts prevent the elementary index-reuse confusion
within that append/truncate construction. They do not prove all external
checkpoint owners, foreign continuations, Rust panic paths or allocator behavior.

**Local seed/publication lemma.** In a successful well-formed start, record n =
origins.len() before candidate_context_seed_with_formal. Its actual seed appends
exactly Origin[n] with created seed, exact occurrence and receipt=None; formal
attachment changes only formal. Since selected relation is already Some,
enqueue_item does not call candidate_enqueue_evidence; it reserves, transfers
an optional Replay acknowledgement and queues, without changing Origins.
Thus the original post-enqueue owner guards hold on this successful path.
This follows from `candidate_context_seed_with_formal` and `enqueue_item` /
`reserve_worklist`, not an assumed transition checker. In v6 recording additionally
uses an optional filtered Origin lookup (`lib.rs:12308–12316`), so a missing
certificate owner no longer adds a receipt-only Result error. These are local
source facts, not global constructor or independently reviewed invariants.

The existing Result error wrappers remove newly created frames and restore
processing pointers (`run_candidate_typed_drain`,
`candidate_context_consume_replay_child`). They are not a proof of Rust-panic
unwinding, whole-state recovery, or all retained replay/restoration owners.
Top-level inference authority requires only necessary abnormal-path safety;
complete rollback/capacity restoration and arbitrary retry are not goals.

## 3. Exact remaining noninterference premises

Let pi erase only certificates while retaining constraints, contexts/residuals,
scoped payload, worklists, drain/Replay ownership, levels, extrusion/intrusion,
resource decisions and publication. A sufficient finite-trace argument needs
each solver transition/result to depend only on pi; optional evidence updates
must stutter under pi, including checkpoint/failure/retry and resource outcomes.
Then induction gives equal projected finite traces. This is a sufficient
candidate criterion, not evidence that all of v6 meets it.

V6 supplies logical append/truncate stuttering, optional post-enqueue recording,
and non-propagation of completion-vector try_reserve failure. It does **not**
establish the following required premises:

- `SourceDrainReceipt::clone` delegates through CauseId/ConstraintOccurrenceId
  to HirOccurrenceId. Its allocation/failure behavior is not established by
  these source pins. Additional clones in start, undo preparation, completion
  and observation cannot be assumed infallible or allocation-free. No clone
  failure or panic was executed, and no definite allocation claim is made.
- `State::bytes` / replay_operation_bytes charge
  `size_of::<new T>() - size_of::<Option<SourceDrainReceipt>>()` for Origin,
  TypedDrainFrame and TypedDrainUndo. Rust layout is not generally additive.
  Equality with the corresponding baseline struct sizes and allocation-capacity
  behavior is not established by this arithmetic or by source inspection.
- Excluding passive storage from an inference cap does not itself bound its
  physical allocation or show unchanged subsequent allocator outcomes. V6 has
  no `total_owned_bytes` symbol and no completion-vector-capacity tally in the
  five supplied source snapshots. Both bytes and enumerated_bytes exclude this
  vector and subtract inline receipts. The implementation handoff's complete
  owned-byte-tally statement is therefore unsupported by these exact bytes.
  A resource-policy/consumer argument and the actual owned-storage accounting
  remain missing; no new accounting policy is approved here.

No layout/compiler/allocator execution was authorized or performed. An exact
remaining premise is preferable to treating a green local lifecycle check as
global noninterference. Even a full certificate-erasure proof would supply
observational safety only, not the parent's missing source/consumer bridge.

## 4. Ordered constructor-to-consumer evidence

Locations in this section use the R173 snapshot; the map/restoration source is
unchanged in v6. V6 only changes receipt completion lookup in the observation.

| Ordered stage | Actual source evidence | Remaining implication |
| --- | --- | --- |
| Fact/Cause -> used seed | source_provider_observation joins store provenance to source occurrence/slot; start_typed_drain retains cause, task, created/selected seed, incoming relation and Replay ack after enqueue; candidate_context_seed appends the owning Origin. | Source-key matches are not universal original Name/body generation or capture coverage. The parent's reviewed original-template lemma retains its premises. |
| Seed -> provider Capture/source bound | Capture::bound (`candidate_scheme.rs:1084–1128`) reads the exact BoundKey fiber, retains each relation and evidence snapshot, and stores orientation and graph-node indices. | The query filters module-callee Capture bounds by seed reachability; it does not prove required bound membership for every provider/route. Local-route alternatives are not covered by this query. |
| Same provider's FreshUse | prepare_candidate_fresh_use (`:1633–1937`) builds one canonical rows/terms map, preserving local/generic guards and older shared anchors; into_retained_parts moves maps together into FreshRoute. | Listing map rows is not applying the selected provider map to the source bound. Another route's copied demand cannot replace that provider. |
| Mapping -> restoration | begin_candidate_fresh_bound (`:1940–1986`) maps bound endpoints through that FreshUse, retains Transport(parent,use_origin,from,to), and requests FreshUse admission with imported antecedent; freshen_candidate_graph_core drives each restoration. | Definitions of Session::candidate_begin_bound_restoration and Session::candidate_drive_bound_restoration are absent from all permitted source-owner snapshots, including v6. Their actual physical append/Replay consumers have not been audited. |
| Provider root -> callee flow | instantiate_candidate_graph (`:1987–2042`) routes its mapped positive root to the exact use component; lib::route (`:17080–17150`) admits/provenances its Fact, constrains it and retains DefinitionUse provenance. | The observation does not authenticate that provider route's lower-fiber lineage into the actual Apply demand under the same use. |
| Actual Apply demand | shadow_apply::admit_candidate_fact (`:2633–2810`) validates recipe operands, constructs actual negative Function(argument,AE,fresh invocation RE,result), retains NativeInterface, admits slot 0 and constrains it; slot 2 emits invocationRE<=ApplyOutputE. | The later checking relation cannot be required to appear in that provider's earlier immutable Capture. Matching endpoints do not supply the missing lineage. |
| Ordered Replay -> consumed ports | candidate_context_begin_replay retains both signed fiber inputs, ordered parents, recipe and child; candidate_function_port_admit retains field and Swap/Preserve; lib Function dispatch creates AE contravariantly, RE covariantly and queues children. | A generated/queued edge or ReplayOperationId is not physical admission or completion. Both actual Replay parents and their fibers remain required. |

The query's reachability closure (`shadow_apply.rs:1285–1335`) follows a Replay
child when either parent is seed-reachable. This is dependency ancestry, not a
proof that both premises, physical emissions and consumers hold. Its global
reachable union cannot license collapsing alternatives, provider/witness
lineages or residual/scoped payloads.

Existing authenticate_demand_transport / authenticate_replay_ancestry retain a
different supported case: an original negative demand captured and copied under
a matching FreshUse, imported snapshot, physical fiber emission, exact ordered
Replay and four ports. They explicitly support zero-step p1=h and q=consumer,
with unique matching source/bound/route, distinct port relations and particular
scoped-transformer assumptions. Preserve those premises; they are not universal
coverage of the earlier positive provider route into a later direct Apply.
Canonical self-pairs, shared anchors, residuals, scoped payloads and nonzero
transport alternatives cannot be rejected or identified merely to reuse it.

## 5. Exact bridge obstruction and mutual TODOs

V6 `shadow_apply.rs:1426–1432` still requires a later direct Apply relation to
be a CapturedBound of the earlier provider. This reverses construction order.
A relation might accidentally intern to an existing canonical identity; that
possibility is not a constructor-authenticated bridge or proof for all source
instances. Deleting the predicate or changing its boolean supplies no missing
edge. V6's harness merely prints the same query and cannot establish that edge.

| Request | Owner and minimal evidence | Falsifier |
| --- | --- | --- |
| R174-NI-RESOURCE | Luna: exact clone/allocation behavior, baseline-layout/capacity equivalence and separate complete physical accounting/consumer policy. Logical completion sublemma above is reusable. | Optional evidence changes solver outcome/publication; subtraction differs from baseline charge; retained optional memory lacks the required bound/accounting. |
| R174-RESTORE | Luna: identify actual definitions of candidate_begin_bound_restoration/candidate_drive_bound_restoration and pin their physical admission/Replay consumers under an authorized input change. No new source file was read here. | Retained admission or Replay ID has no matching actual mapped bound/readback/consumer, or names a different source_bound/use/ordinal. |
| R174-FWD-JOIN | Luna: minimal provisional retained/borrowed provider-root route -> callee lower-fiber -> actual demand upper-fiber -> ordered Replay -> consumed FunctionPorts certificate, retaining both parents, use/cause/owner, scoped/residual state and ordinal. | Wrong/sibling provider, switched FreshUse owner, Replay-only source seed, swapped parents, later relation presumed in earlier Capture, merged alternatives, or missing consumer. |
| R174-ALL-ROUTES | Luna: after that join exists, original quantified coverage of mapped Name/body admission and per-use forwarding joins. | A permitted repeated/local/shared-anchor/self-pair/extruded/scoped/failure/pending route lacks its own authentic premise although R171 passes. |

These TODOs request evidence, not authority to edit extra owners or expand the
source domain. The present source envelope stops at those suppliers. The full
parent, native correspondence and production gates remain OPEN. Fresh review
belongs to Luna; this author cannot certify its own contribution or combined code.

## 6. Inputs, provenance and checks

Baseline metadata: proof commit `7ec64a3788175913a2be46331cf0f64c6bd5b407`;
activation HEAD `e9a7a4fef3d6872fa0596646393a7c0473b3687b`. No Git command checked
these metadata. Luna supplied/froze all snapshots and authored the R174 code;
historical individual source authors are UNKNOWN. R173 historical proof is not
rebased onto candidate bytes. Baseline/R173 source diffs are static evidence.

All SHA-256 pins below were verified. Baseline/R173 directories contain the
four named solver owners; R174-v6 additionally contains the harness.

```text
contract rev2 01df299dfd16276d1c0bfc376946ad0dcab47d92ebb1916307fe36ccc33e28d8
proof input rev2 5013ed335a8141599364a072167e4dea571c9d77438356a56f50215874fb3c36
R171 fixture cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f
/tmp/r174-inputs/baseline-7ec64a378/:
lib.rs c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985
candidate_context.rs d884c20a98140da2a737d65f61faa97491bd9a2af7870bf3f0ea7dd428e9ffeb
candidate_scheme.rs 9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225
shadow_apply.rs 13ae8de60293b91e24659090649ff84002f5632a8909451d3f7bd8492b61bea5
/tmp/r174-inputs/r173-candidate-v4/:
lib.rs c005b99c1aa6da3c6b203e19c37f8b99700618815528f33d67cbf70941df78f5
candidate_context.rs 723cc253090ad2b4a0c67a1a17c57bc0587b26e4dc4d90a642f45ab0d1f468fa
candidate_scheme.rs 48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25
shadow_apply.rs 7a4c64d3783496029225be043ea8914543ceff1841caed5fcec19d68dcfb4932
/tmp/r174-inputs/r174-candidate-luna-v6/:
lib.rs 24f480355979ee5d96305a08abf6aab67025ede32c2a1575b779e46f5e23b436
candidate_context.rs a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733
candidate_scheme.rs 48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25
shadow_apply.rs 2b0e46f28c328172477ac263360f4f3d01d27714dc62cd93235b8e3b1fe4e9ff
r174_forwarding_bridge.rs 920275d9301ace568634d5c1401f93a9ffc01605a7c562e2d4998e85d1109d3b
implementation handoff at v6 read e6dec0fd9121a4eaf150e85dad778639ed7c04184a7c4690c627e53948ec5fa1
```

Superseded consulted inputs: v2 lib c405c998c497a128ca04c671b8ccef33ab9c90c3cb272f60d1d27c4eedbc7516,
context e2159dc8b8507d977d48c5e2cffb15f883866baa76d3c7756eb75459e34b3b54;
v3 same lib, context 156ecfcc7e45721e852d2fb7b278119cfdf639782dc4e650ec8f1e6946db49c3;
v5 lib a7af045e84f938fe58372bd353e4ed2f67dc828cd9c65cd2c4578f2f4174463a,
context same as v6. Their scheme/shadow/harness pins equal v6. V5's out-of-scope
duplicate Origin assignment was reported to Luna and removed in v6. V1/v4 were
not read. No superseded candidate is the final proof target.

Authority pins: goal-driven-sprints e50f5d4f79814c87af56e7dc34ddb6ab968abb523826c72ecdc40a8920397c0a;
agent-loop README 1379059577f4469ed930c0fc130e5cd169401cf9188dfcbbc482b92b43daebbf;
sprint skill b6f4a50703928020607edebe1c8b138fb98a0378220f00b7c190dba9fc068515;
proof skill db55dfb7568805ac6b6372fe8bc05cc00731ae5b5ed33c6af72007a7ce885810;
inference authority 7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81;
sprint decision 2dfeb555c913d3142078de535ee4b7f68e9a27f2b91a5f0bb82d4d867db4fc4e.

Checks: byte hashes; source and constructor-order reads; baseline/candidate
diffs; symbol searches; candidate logical completion derivation. Zero builds,
tests, compiler/evaluator/Yulang2 runs, probes, network, Git or nested CLI.
One attempted artifact write used unavailable `python` (exit 127); it wrote
nothing. Subsequent artifact preservation uses python3 only for bytes/hashes,
not a solver model or test. No scratch path was created by this worker.

Grant: 1200 seconds, Astra 0. Exact runtime metadata UNKNOWN; charge the full
1200 seconds. Clock observations begin 2026-10-20 17:00:23 UTC, not a trusted
launch timestamp. Requested model Sol/high; effective model and effort UNKNOWN.
Only this note and the assigned proof inbox are written. The inbox carries the
final freeze/hash, stop receipt and all exact output paths.

## 7. Preserved assigned input revision 2

Exact original input bytes follow between markers, including their final LF.
Their SHA-256 is the proof-input digest above.

<!-- R174-INPUT-REV2-BEGIN -->
# R174 constructive proof packet — revision 2 candidate

Sprint: `rollback-inert-forwarding-bridge-20261021-r174`, contract revision 2,
SHA-256 `01df299dfd16276d1c0bfc376946ad0dcab47d92ebb1916307fe36ccc33e28d8`.
Requested role: configured
`prover`, Sol/high. Luna owns adoption and final review; this author cannot
review the combined result.

## Parent claim and hypotheses

Parent: `notes/theory/2026-10-15-computation-forwarding-preservation.md`
§§1,6–7, SHA-256
`d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`.
Preserve its source domain, all quantifiers, shared satisfying assignment, open
incoming E, finite chains, repeated calls, simultaneous entries and every
finite prefix. The source is the unchanged R171 fixture, SHA-256
`cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f`.

Candidate dependencies: proof baseline commit `7ec64a3788175913a2be46331cf0f64c6bd5b407`;
activation metadata HEAD `e9a7a4fef3d6872fa0596646393a7c0473b3687b`. Read only
the immutable snapshots below; do not read the mutable checkout as proof input.
R173 review receipt in
`tasks/agent-loop/current.json` and handoff rev4. Proof rev1 from R173 applies
only to its original baseline bytes.

Exact read-only source inputs, SHA-256:

```text
c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985  /tmp/r174-inputs/baseline-7ec64a378/lib.rs
d884c20a98140da2a737d65f61faa97491bd9a2af7870bf3f0ea7dd428e9ffeb  /tmp/r174-inputs/baseline-7ec64a378/candidate_context.rs
9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225  /tmp/r174-inputs/baseline-7ec64a378/candidate_scheme.rs
13ae8de60293b91e24659090649ff84002f5632a8909451d3f7bd8492b61bea5  /tmp/r174-inputs/baseline-7ec64a378/shadow_apply.rs
c005b99c1aa6da3c6b203e19c37f8b99700618815528f33d67cbf70941df78f5  /tmp/r174-inputs/r173-candidate-v4/lib.rs
723cc253090ad2b4a0c67a1a17c57bc0587b26e4dc4d90a642f45ab0d1f468fa  /tmp/r174-inputs/r173-candidate-v4/candidate_context.rs
48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25  /tmp/r174-inputs/r173-candidate-v4/candidate_scheme.rs
7a4c64d3783496029225be043ea8914543ceff1841caed5fcec19d68dcfb4932  /tmp/r174-inputs/r173-candidate-v4/shadow_apply.rs
```

## Claim

Constructively establish whether the source-to-consumer path can be represented
from actual retained producers in this order:

`source Fact/Cause and used seed → provider Capture/source bound → provider's
own FreshUse mapping/restoration → callee flow → actual Apply demand → ordered
Replay/FunctionPort consumer`.

Separately establish observational noninterference of any certificate across
completion, checkpoint, rollback, retry, failure/unwind and repeated invocation.
If an owner fails to retain a required edge, report the first exact constructor
and prove only that bounded obstruction. Apply useful lemmas to the original
parent and name the exact remaining premise and owner.

## Method, exclusions, falsifier

Trace real constructors and consumers in the pinned code. For every edge, give
its source record, generated record, transport/restoration relation and actual
consumer. Preserve alternative routes, canonical self-pairs, shared anchors,
residual/scoped payload and invocation ordinals. Treat Captured provider state
as earlier than the enclosing Apply's fresh relation. Do not infer the bridge
from endpoint equality, relation membership in an earlier Capture, or a green
fixture run.

Falsify a proposed chain with any missing/ambiguous producer identity, a route
that changes Capture/FreshUse owner, a Replay edge substituted for a direct
source seed, a completion/rollback/retry trace that changes solver behavior, or
an Apply relation shown to arise only after the required Capture snapshot.
Do not assume the implementation repair; the pinned R173 source is a counterexample
input and the R174 implementation is a separate candidate lane.

No code edits, compiler/build/test/evaluator/Yulang2 execution, probe, network,
nested CLI or descendants. Requested grant: 1200 seconds, several related proof
stages under the same lease, Astra 0. Reserve is charged on issue; UNKNOWN
elapsed is charged in full. Stop and return a precise missing owner if no
constructor supports a required edge; preserve all parent gates OPEN.

Exact outputs: this packet and
`notes/theory/2026-10-21-r174-rollback-and-forwarding-bridge.md`. Requested and
observed model/effort, consulted hashes, checks/omissions, descendants and
write-stop receipt must be reported. No independent self-review.
<!-- R174-INPUT-REV2-END -->

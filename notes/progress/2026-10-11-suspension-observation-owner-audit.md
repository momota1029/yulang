# Suspension mutation and observation owner audit

Status: **unreviewed complementary research; lifecycle incomplete**. This is a
bounded static source inventory, not a constructive proof, independent review,
or permission to mint a production certificate.

## Objective, authority, and pinned inputs

Identify existing owners of mutation, observation, withdrawal/recomputation,
route rollback, and accounting needed by the Authoritative private candidate
suspension contract, especially §§5–7. The accepted design requires exact
dependency identities and a lifecycle generation distinct from intrusion
generation; withdrawal precedes reuse, recomputation precedes the saved next
child, and SCC publication waits for every member. The approved language meaning
and ordinary identity behavior are not reopened here.

Primary baseline: `919864319bf216d9b8803dd1095941a571f78e78`, with the primary's
explicitly revised frozen working-tree snapshot below. These are dependency
hashes, not a claim that all these bytes occur in the baseline commit.

| Input under `crates/yu-solver/src/` | SHA-256 |
| --- | --- |
| `candidate_context.rs` | `bc7e25c14e913d5f1c487723ead0fbbaf696bce80a1e6b756b7af4c04d6ebadc` |
| `lib.rs` | `42bb81741d129cca8d9cf64a25f0a54c11fcf4cccc022f66c131c321752aa9de` |
| `candidate_context_tests.rs` | `1a82541f9d06e1d414210e370dae0828e50508c88c52aecd61585345f29a1eb3` |
| `candidate_effect.rs` | `7e8e077f13c4a094565cc199a0e643fad2d04c920b449058b33ebb4d048cd360` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `candidate_scheme.rs` | `7d3169a68d2413b58228f122c1e92a21d828e1a44e41743f4458eabb90ca580c` |

`notes/design/2026-10-11-private-candidate-suspension-contract.md`:
`734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d`.
The accounting repair superseded the packet's initial context/lib/test hashes.
Active-file reading was paused during that repair; cited active ranges were
re-read at this snapshot. Stable effect/intrusion/scheme inputs stayed unchanged.

## Claim class and exact premise

**Bounded characterization:** the six audited files implement physical mutation,
provenance, ordinary completion, retained replay/restoration, and synchronous SCC
staging. They do not yet implement the certificate observation owner inventory
required by §§5–6. `candidate_context::State` (604), `EvidenceDependent` (358),
intrusion `State` (9), scheme `GraphState` (6), and `Graph` (34) contain no such
lifecycle registry. `retained_input` (812) returns incomplete input, including
unconditional filter, readiness, and dependent-observation gaps (958–961).
The inspected consumers cannot currently acquire a production certificate from
that interface. Existing reverse provenance edges therefore do not establish
the future registration inventory.

**Conditional obligations:** the rollback and publication seams below become
counterexamples only if new suspended execution retains pre-route mutable frames
or previously published certificate-dependent graphs. Current typed frames are
pushed and popped within one synchronous drain; no live certificates were found.
This note establishes no current stale-certificate compiler failure and no
universal absence result outside the bounded source inventory.

## Mutation producers and existing consumers

Line numbers below refer to the frozen inputs above; paths are relative to
`crates/yu-solver/src/`.

| Mutation family and implemented owner | Existing consumers and retained identity | Missing lifecycle owner |
| --- | --- | --- |
| Context/relation/origin admission: `candidate_context.rs::context` (1913), `relation` (2075), `dependency` (2102), `candidate_context_seed` (2290). Origin is appended even when a relation already exists. | Retained-input traversal, processing relation, context execution/replay; raw relation and origin identity survive ordinary deduplication. | Exact mutation hook and support registration independent of allocation and SCC generation. |
| Dependency-only Function port: `candidate_function_port_admit` (2351–2402); Derived admission at 2393, distinct FunctionPort at 2395. `dependency` deduplicates before mutation (2103–2105). | Diagnostic/context dependency traversal; typed Function dispatch retains admitted relation in `pending` before enqueue (`lib.rs::candidate_step_function_dispatch`, 12243–12265). | First new FunctionPort incidence must invalidate its dependent certificate even if Derived and child relation already exist. Exact duplicate must remain inert. |
| Attachments, filter replay, discharge: `attach` (2203), `post_check_context` (2217), `candidate_context_execute_relation` (2538); existing filtered origin/replay path at 2575–2589; discharge/residual state at 2595–2603. | Context execution can reuse discharge (2561); typed drain retains its consumed-context marker. Bound fibers are traversed in exact context. | Certificate support for each registration/discharge result and withdrawal before cached execution reuse; recomputation of earlier completed context observations. |
| Bound fiber/origin/evidence admission: `candidate_context_bound` (2608), `candidate_bound_origin_with_evidence` in `candidate_effect.rs` (341), `BoundEvidence::admit` in context (509), `emit` (559), `transform` (568), `recipe` (591). | Bound groups, exact fibers, ordinary physical bounds, replay, graph capture snapshots. Duplicate origin admission may still add evidence. | Selective support ownership distinguishing accepted physical bounds from certificate-derived results; alternate support cannot be reconstructed from endpoint equality alone. |
| Evidence imports and transport: `candidate_context_transport_witness_with_evidence` (2879), `candidate_context_fresh_transport` (2842); freshening imports/remaps in `candidate_scheme.rs::freshen_candidate_graph_inner` (899–1179). | Graph-bound evidence and attached context used by restored bounds and replay. Transport keeps exact source keys; it deliberately adds no diagnostic edge (`dependency`, 2115). | Imported/transformed evidence invalidation hook, authentication witness, and dependencies of every consuming observation. Diagnostic reachability cannot substitute for this owner. |
| Capture incidence and views: `candidate_capture_incidence` (398), `candidate_splice_capture_incidence` (428), `candidate_register_capture_bound` (452), signature view/copy/remap (632, 705, 731), contribution (763) in effect. | `Capture::expand_row` in scheme (492; incidence traversal 544–550), graph-bound capture (445), operand checks (787), conflict construction/replay (503, 558). | Dependency support for captured graph slots and eligibility, plus dirty/withdraw/recompute callbacks on incidence mutation. Captures contain frozen evidence; their origin support is not registered. |
| Source annotation/operation constructors: effect `candidate_operation` (685), scoped `candidate_annotation_variable` (857), `candidate_formal_effect_variable` (878), formal pairs/ports (933, 953), `candidate_formal_annotation` (972), local/root/ascription paths (1016, 1071, 1085), negative empty bundle (1171), computation effect (1206), signature value/effect (1246, 1338). | Scoped maps and formal-domain memo feed source annotation lookups; constructors emit Function terms, bound/view/attachment mutations through owners above and publish local terms. Formal domain and named rows preserve source scope; whole computation effect checks remain ordinary edges. | Any certificate-consuming scope/domain memo requires an explicit support owner; these maps are not currently certificate observations. New signature fiber/attachment/support admissions must pass the same mutation hooks. Constructor recursion/local scratch is not a suspended source continuation. |
| Intrusion/extrusion: `retain_extrusion_parent` (171), `settle_candidate_intrusion` (358), `merge` (513–605) in intrusion; canonical bound transport in context (2822). | Merge transfers physical bound sides, capture incidence, representatives, contexts, and replay; intrusion generation advances (594), root reopened (597). | Separate lifecycle generation for evidence-only mutation and all registered observations. Suspended raw endpoints must canonicalize at resume while retaining original count/order (§4); cross-component incidence remains a proof prerequisite. |

This inventory includes mutating evidence/provenance operations even when no
ordinary relation or physical-bound insertion occurs. In particular,
`candidate_transfer_bound_origins` (effect, 462–501) explicitly records
`MissingOriginAssociation` (491–497). Evidence admission also retains gaps for
unavailable antecedent/authentication witnesses. Reverse edges alone cannot
identify all supports or decide which derived bound to withdraw.

## Observation, withdrawal/recompute, and route owner inventory

| Observation | Implemented owner | Implemented rollback/accounting | Absent owner required before certificate use |
| --- | --- | --- | --- |
| Typed pair memo and completion | `lib.rs::record_typed_pair_admission` (12326); diagnostic settlement `complete_diagnostic_delta` (12555). `pair_is_current` (11362) compares intrusion generation; `candidate_reopen_root` (11350) sets Pending. Intrusion `mark_candidate_pair` (223) and `journal_candidate_memo` (257) own generation stamp and memo replacement. | New memo keys in route journal; saved prior memo including children in intrusion undo; reserve-before-admission at 12326. | Certificate support registration, dirty/withdraw state, and retained recomputation task for every dependent completion. Intrusion stamps cannot cover FunctionPort-only mutation. |
| Generated replay child batch and replay progress | Context `candidate_context_begin_replay` (2705): frozen ordered children, replay-progress advancement (2768), `queued=0`, `consumed=0` (2775). `transfer_replay_child` (1737) advances queued; `complete_replay_child` (1772) advances consumed after successful typed drain. | `ReplayOperationUndo` saves queued/consumed/retired; rollback (1530); batch bytes and ack buffers in `replay_operation_bytes` (1661). Reserve/check before dequeue in lib (11874–11904). | Dependencies for both generation and consumed result, selective withdrawal of old generated/consumed observations, and recomputation before saved child. Generated progress is not completed work. |
| Physical bound restoration/product progress | Context `BoundRestoration` (68): emission, raw owner/polarity/bound, saved opposite count, next index, replay, source occurrence/cause. Existing cursor undo at 1524. | Accepted bound/ordinary row journal plus restoration/replay undo; original physical emission need not repeat on retry. | Certificate-dependent product/result ownership and recomputation ordering. Resume must reread current canonical opposite vectors at saved indices, not freeze all endpoints (§4). |
| Typed drain / Function dispatch | Context `TypedDrainFrame` (28), `begin_typed_drain` (1650); lib typed drain (11809–12233), admitted-child `pending` and enqueue stages (12243). Current result has only Complete/error, then pops frame (12214). | Frame capacity/ack capacity accounted (1661); checkpoint saves frame vector length (675); rollback truncates (1523). Current synchronous frame creation is route-local. | Suspended outcome, preexisting-frame field undo, dirty dependency checks before each consumer, wait/recomputation frame and original-order barrier. Source/SCC, freshening, and extrusion continuations also lack persistent frame owners. |
| Derived bounds | Effect admission/transfer and context bound/evidence owners above; physical row insertion and restoration own accepted state. | Nested evidence checkpoint/undo (context, 392–441), effect checkpoint/undo (162–229), ordinary row journal. | Precise observation support and selective removal/recompute preserving exact underlying relation/new accepted edge and independent supports. No certificate-specific derived-bound registry exists. |
| Captured member/local graph slots | Scheme `Graph` (34), `Capture::bound` (445), `expand_row` (492), `capture_candidate_graph`; graph snapshots retain evidence and exact relation identities. `install_candidate_local_term` (1238) rejects an occupied slot. | Graph bytes (154), `GraphState::refresh_bytes` (167); newly installed local slot indices journaled (1245). | Certificate support/stamps for capture; withdraw/replace/restore prior member/local contents; simultaneous old, staged, and rollback graph accounting. A captured snapshot is not a registered observation. |
| Incoming/open/local use eligibility | Scheme `route_candidate_graph` (872) requires a stored slot, then recaptures its live root (884); `route_candidate_open_use` (863) checks active roots/uses; local routing (1264) requires its local slot. Lib `route_incoming_inner` (16052) delegates candidate path. | Fresh-route/local-route length journal; routed-use owners and route transaction. Recapture protects against blindly consuming the stored bound snapshot. | Eligibility dependency/generation guard and withdrawal before use. Recapture from live root does not prove the source member remains publishable after certificate invalidation. |
| SCC group publication/frontier | Scheme `execute_candidate_graph_plan` (767) completes member source actions, captures all into `staged`, then installs all slots (834–836); active roots/uses established (795) and cleared (839). | Transient orchestration bytes (791), staged graph byte sum (827), retained byte update (837). | Persistent suspended source/SCC frontier, dependent completion barrier, generation-supported group eligibility, old-slot/frontier rollback, and disjointness authorization for independent components. Existing staging is synchronous, not a suspension publication protocol. |
| Final observation projection | Lib `finish_observations` (16673–16720) reads current physical bounds. | Ordinary physical-state transaction, no certificate observation record. | If it consumes accelerated results, register that dependency and prevent final reuse/publication until withdrawn results are recomputed. |

The aggregate route owner is `lib.rs::RouteMutationJournal` (8104), with
`begin_route_transaction` (8962), `with_route_transaction` (9157), and rollback
(9285). It contains row/store undo, route lengths, new local slots, nested
intrusion/effect/context undo, typed pair/error keys, generations and accounting.
It contains no lifecycle generation/certificates/registrations/dirty sets,
withdrawn observations, wait/recomputation frames, prior member graph slots, or
active source/SCC frontier snapshot. Intrusion undo (29–44; rollback 103) does
not restore `active_roots`/`active_uses`. Local-slot rollback (lib, 9321) only
clears newly installed slots, consistent with the current no-replacement API.
Scoped annotation/formal-domain owners reserve their live and undo maps before
publication (effect, 857–899 and 995–1008); effect checkpoint/rollback (162–209)
removes their route-added keys and restores owned-byte accounting. This is
implemented ordinary publication undo, not certificate withdrawal/recomputation.

## Minimal discriminating sequences

These are source-grounded test specifications, not executed experiments.
Existing test assertions are evidence of coverage intent only.

1. **Dependency-only incidence versus allocation/equality hook.** Preintern
   parent and identity child, including their Derived dependency. Admit new
   FunctionPort dependency for that existing pair. Relation/context allocation,
   diagnostic edge count and intrusion generation remain unchanged while exact
   dependency incidence grows by one. Repeat exact admission: no growth. Roll
   back first admission: incidence restored; retry: exactly one new incidence.
   Existing test `function_port_identity_incidence_changes_without_new_relations_or_intrusion_generation`
   (tests, 3153–3220) supplies this mutation witness. A lifecycle hook keyed only
   to relation allocation or intrusion generation fails its first step.

2. **Completed sibling invalidation (synthetic certificate prerequisites).**
   Under generation g, complete child A and register its memo/derived result,
   generated replay batch, captured slot and eligibility. Pause before child B.
   Admit the dependency-only incidence above. Withdraw exactly g-dependent
   observations while keeping the relation, original origin and accepted bound.
   Recompute A before B. If A suspends, B stays blocked. No second use identity
   or emission; repeated drive without relevant mutation is stable. Inject
   failure during withdrawal and recomputation and require exact pre-route
   state/accounting. This discriminates a real recompute owner from merely
   clearing memo stamps. No current certificate API implements this sequence.

3. **Generated versus consumed replay.** Queue one retained replay child twice:
   generated/queued stays one, consumed zero until successful typed drain.
   Inject failure after an acknowledgement: cursor returns to its prior value,
   retry consumes once. Existing tests (1641, 1725, 1795) cover queue/consume,
   saved restoration and rollback without re-emission. Add certificate
   invalidation after consumed child A to sequence 2; cursor rollback alone does
   not establish observation withdrawal or recomputation.

4. **Prior-frame rollback, conditional future witness.** A future suspension
   leaves frame F before a route checkpoint. Resume F, changing `current`,
   `stage`, `function.pending/next`, ack buffer/`completed_acks`; then fail route.
   Present rollback only truncates to the old frame count, so it cannot restore
   F's prior contents. This is a conditional structural counterexample, not a
   current synchronous bug: present drain frames do not cross the transaction
   boundary. Require old-content undo before enabling that new transition.

5. **Publication and replacement, conditional future witness.** Begin with
   two published dependent member graphs. Invalidate their certificate, retain
   a new bound, finish member A but suspend member B. Neither slot nor any
   incoming-use eligibility becomes visible. Fail after staging/replacement:
   restore the exact old slots, frontier, eligibility and retained/rollback
   bytes. Retry must publish both together. Current local install cannot replace
   a slot; current member assignments have no old-content journal. This test
   needs the missing suspended group owner, not just synchronous `staged`.

6. **Producer-hook discrimination beyond FunctionPort.** Independently admit
   a new origin for an existing relation, new attachment/filter incidence, new
   evidence import/transform, and new capture incidence without an SCC merge.
   For each, the hook must dirty only registered dependent observations; exact
   duplicates must not advance lifecycle generation. Also suspend immediately
   after FunctionPort admission before enqueue: preserve pending relation,
   parent frame and next index. The existing owned-dispatch test (3940–4007)
   covers the synchronous relation/enqueue seam and rollback, not certificates
   or source-owned suspended fresh-use restoration.

## Residual bridge, limitations, and next action

The unproved owner inventory is exact: every certificate consumer and every
support identity linking the producers above to memo/completion, replay batches
and consumed progress, derived results, captured slots, eligibility, final
projection and group publication. No registry currently lets this audit prove
that all consumers register, that all relevant mutations dirty them, that
selective withdrawal preserves alternate supports, or that recomputation is
ordered ahead of continuation. `EvidenceDependent` has only Admission and
FiberTransform cases; this does not classify the other observation owners.

Production readiness/filter/transport/dependent witnesses and exact source
recognition remain prerequisites. The required genuine source-owned fresh-use
test with multiple opposite products, late unsupported Function/swap, existing
memo/publication, rollback and supported retry (§7) is not supplied by synthetic
cursor tests. Ordinary identity routes remain an explicit regression condition.
Cross-component mutation of suspended incidence and source-to-owner completeness
require the constructive lane; this static inventory cannot discharge them.

Recommended next action: implement one explicit observation/support registry
and its mutation hooks, selective withdrawal/recompute barrier, and prior-frame/
graph/frontier transaction owners before enabling certificates; validate with
the discriminating synthetic sequence, then the authentic §7 source sequence.

## Checks, resources, and commit packet

- Method: one bounded static pass over the assigned six files and governing
  contract; targeted `rg`/`sed` reads and SHA-256 checks. No source, Cargo,
  compiler, tests, executable model, Git commands, or delegation.
- Final snapshot hashes matched the primary's supplied values. Assertions in
  inspected tests were not executed. Oracle independence: no executable oracle
  was used; the independent criterion is the approved contract, with the source
  representation supplying the bounded correspondence and conditional witnesses.
- Seeds/ranges: none; no randomized sampling. Resource budget: 20-minute lease,
  one static pass; exact accumulated wall time unavailable after context
  compaction. No heavyweight processes or measurement budget used.
- Changed path: only `notes/progress/2026-10-11-suspension-observation-owner-audit.md`.
  Artifact frozen for review; review status **unreviewed research**.
- Baseline SHA: `919864319bf216d9b8803dd1095941a571f78e78`; final dependency
  hashes are the table above. The primary's accounting repair changed context,
  lib and tests from the original packet; this lane changed no dependency.
- Proposed checkpoint message: `research: inventory suspension observation and transaction owners`.
- Proposed shared-record delta, intentionally left to primary/curator: add this
  bounded owner inventory as unreviewed complementary evidence; keep lifecycle,
  producer recognition and source fresh-use restoration gates incomplete; track
  observation registration, recompute ordering and conditional prior-frame/graph
  rollback owners as remaining obligations. No authority/index/task/theory or
  question-board records were edited.

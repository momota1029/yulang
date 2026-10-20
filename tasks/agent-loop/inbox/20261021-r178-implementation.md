
## Luna analysis — revision 3, frozen source findings

Contract: `tasks/agent-loop/sprints/registration-consumer-invariant-20261021-r178.md`, SHA-256 `a2064d02c7f9f9377313d28bfcd2f33a811513f25014613ab9544b25295f92b4`.
Proof packet: `tasks/agent-loop/inbox/20261021-r178-proof.md`, SHA-256 `45867bcf64b8fd1a2a4b95f74eb451fd1eaffc2f51074f33aab4f0a04e1c4858`.
Candidate roots are immutable snapshots only; the eleven source pairs match every listed hash,
file mode `0444`, root mode `0555`. The new `candidate_value_graph.rs` contents
were first read after both CLEAN reviews and Luna activation. No checkout source
was substituted.

### Registration and direct module-use correspondence

`candidate_source::emit_candidate_source` first verifies the passed
`LocalSource` pointer is the HIR-owned source for its root and that every
expression occurrence belongs to that HIR (`candidate_source.rs:827–849`). It
then calls `Graph::retain_source`. That owner traverses the original source
expressions and binding initializers. Resolved Name references add source-owner
to target edges; initializer bodies are assigned to their `Local` owner. Every
Apply creates one checking key `(Apply occurrence, slot 0)`, an inverse event
entry, and an origin/receiver pair. Name and Lambda occurrences do not each get
checking events. This is role separation: the graph records source reference
incidence, while the checking event identifies Apply occurrences used to
qualify recursive calls. `seal` computes SCCs and `qualifies` means the event's
source owner and resolved callee have the same source component. Unresolved
callee forms fall back to their expression vertex; no inference is made about
uninspected HIR resolution cases.

For a direct `ModuleDef` callee, collection creates a `DefinitionUseId` from
the same source occurrence and sets `use_value_component` from that occurrence's
component position (`lib.rs:1358–1387`). The Apply recipe takes its callee from
that expression endpoint (`candidate_source.rs:1388–1428`); ModuleDef Name
endpoints are the same occurrence component (`candidate_source.rs:893–901`).
`instantiate_candidate_graph` constructs the exact FreshUse route with the
`DefinitionUse`'s `use_value_component` as its upper endpoint and retains the
same `DefinitionUseId` (`candidate_scheme.rs:1987–2045`). `admit_candidate_fact`
checks the source call and recipe occurrence/endpoints, constructs the native
Apply demand, and stores the exact callee endpoint in `NativeInterface`
(`shadow_apply.rs:2631–2774`). This is a constructor-derived direct module-use
identity bridge, not an endpoint guess.

The established bridge is limited to this ModuleDef route and endpoint
identity. It does not by itself prove that every original Name/body inequality
is represented in the captured FreshUse bounds, or that provider constraints
survive arbitrary polarity/extrusion and both consumer inputs. Local-formal
Apply paths use a different constructor. In particular the ModuleDef call has
no `formal_name`, so no `DirectionalIntroduction` is made and the context seed
does not acquire a `ScopedDemand` carrying that call/use identity
(`shadow_apply.rs:2707–2733`; `candidate_context.rs:3332–3398`). The
demand-specific Replay authenticator therefore cannot certify this direct
module route merely from its successful NativeInterface comparison. This is
missing proof evidence, not a demonstrated inference failure.

### Pending work and reuse

On successful typed-drain execution, the concrete work owner follows this
sequence (`lib.rs:12130–12258, 12320–12495, 12740–12856`): the queue item is
retained as `frame.current` before fallible transport/dispatch; a Function pair
retains four ordered field pairs in `FunctionDispatch`; each child first
retains a `pending` `TypedWorkItem`, then `enqueue_item` succeeds before
`next` advances; popped replay acknowledgements are retained in the frame
before dispatch. Empty queue is not completion while intrusion remains dirty:
`settle_candidate_intrusion` runs and the drain stays in Transport until clean
or new work is queued. Diagnostics and acknowledgement stages follow only
after that; replay child acknowledgements and return receipts are processed
before the drain frame is removed. This supports a local pending-work
conservation argument for successful, no-rollback drain segments.

`mark_candidate_pair` publishes the current-generation marker during typed
pair admission, before Function children are installed or enqueued
(`lib.rs:13100–13170`; `candidate_intrusion.rs:423–455`). The marker is not a
discharge receipt. Its safe use as an in-flight duplicate guard depends on the
active item/frame or queued task retaining the work. Current-pair reuse checks
typed memo membership plus this generation marker (`lib.rs:11593–11603`).
Reopening a root sets diagnostic completion back to Pending. Valid journaled
route rollback records/restores completion entries and typed-memo changes;
unwind and all publication traces are outside this local derivation. The
source does not yet establish that every legitimate current/canonical/self/
coalesced/rewrite/shared-anchor reuse either retains justified pending work
under the same source/use lineage or carries prior semantic discharge.

The Function expansion itself retains the two ordered inputs in its exact
field construction (`lib.rs:12690–12745`). Context Replay records
`child`, `lower`, `upper`, `lower_input` and `upper_input`; drain acknowledgements
wait for child processing. This is a producer-side structural derivation, not
proof that every source inequality from the same provider/use reaches both
ordered inputs and the actual consumer through arbitrary finite chains. The
special demand authenticator checks both inputs and typed ports only in its
supported captured-demand case; its source comments explicitly retain the
missing `p1→h` constructor and require the zero-step case
(`candidate_scheme.rs:475–650`).

### Luna outcome

**NO_SAFE_CODE_SLICE.** Registration now has an exact source-owner explanation,
and direct ModuleDef call/use identity has a construction-derived bridge. A
strictly smaller source-to-consumer theorem still needs proof of captured bound
adequacy, provider/use identity through polarity and physical Replay
construction, both ordered inputs, and semantic current/reuse discharge for
the original domain. No source-qualified counterexample or implementation bug
was established. Do not relax the existing failed membership checks or infer
that successful finite examples establish universal capture coverage. Resource
layout/capacity, allocator, Arc/refcount, rollback, publication and unwind
erasure remain separately OPEN.

Inspected immutable owners: `candidate_value_graph.rs`, `candidate_source.rs`,
`candidate_context.rs`, `candidate_intrusion.rs`, `candidate_scheme.rs`,
`shadow_apply.rs`, `lib.rs`. No other source owner was needed for this scoped
analysis. Tests/builds/probes/compiler/evaluator/Yulang2 execution, code edits,
network, Git, nested CLI and scratch paths: **NONE**. This is source analysis,
not an independent review or theorem certification. Full Luna lane grant
**600s charged**, elapsed UNKNOWN, zero remaining; writer remains active only
to integrate proof outcome and closeout.


### Luna integration — revision 3, frozen proof result

Proof revision 2 is frozen and the worker is STOPPED. Its note hash is
`c59a06abb002ba76b5b76887edcebb89f7398a99eb3d1ffe6d8787d3908d0291`;
proof handoff hash is
`45867bcf64b8fd1a2a4b95f74eb451fd1eaffc2f51074f33aab4f0a04e1c4858`.
The proof worker reports that all 22 source hashes/modes matched before semantic
reads and at freeze. Requested Sol/high; observed model/effort UNKNOWN; full
1380 seconds charged. No tests, executions, source edits, Git, network, scratch
or descendants.

The proof constructs these scoped correspondences: Apply slot-0 registration
joins the actual ApplySourceInput, NativeInterface and direct typed-drain seed;
direct ModuleDef provider-use and Apply share the exact source-constructed
callee component; and administrative work is retained through current/pending
fields, queue transfer, Replay acknowledgements and valid rollback. This
reduces the corresponding premises when applied to the unchanged parent.

The earliest universal gap remains the route from each original required
Name/body inequality to this provider's Capture or a justified shared anchor.
Coverage of both ordered Replay inputs and semantic discharge on current/reuse
remain OPEN. A direct ModuleDef route has no ScopedDemand identity producer for
`replay_demand_rows`; this is a certificate-availability limit, not an
inference-failure witness. Resource erasure remains separately OPEN. No
source-qualified counterexample or implementation bug was established.

**R178 result: NO_SAFE_CODE_SLICE.** No code, test/build/probe, compiler,
evaluator or Yulang2 execution is authorized or performed. Parent, A/B,
source/native, implementation and production gates stay OPEN.
Luna analysis grant: 600 seconds charged, elapsed UNKNOWN.


### Closeout receipt — revision 4

Independent final reviewer `/root/r175_final_review` returned CLEAN for the
contracted unfinished-research result. Review input pins: current state
`a20ce7730270b6cbe3d9d9ac4bd453faa1512f4e1ce4075cb042e94494bbdb07`,
contract `a2064d02c7f9f9377313d28bfcd2f33a811513f25014613ab9544b25295f92b4`,
proof handoff `45867bcf64b8fd1a2a4b95f74eb451fd1eaffc2f51074f33aab4f0a04e1c4858`,
Luna handoff revision 3 `776e9e3b7b7540f326d87208eb95197b70ef44e556d94d98605c2956ea9e13cb`,
and proof note `c59a06abb002ba76b5b76887edcebb89f7398a99eb3d1ffe6d8787d3908d0291`.
All 29 review targets were unchanged at entry/exit; 22 source hashes/modes
matched the contract, snapshots remained `0444` with roots `0555`, and parent
and fixture pins matched. No parent theorem or compiler integration was approved.

The reviewer identified two minor metadata issues. This revision supplies the
contract and proof packet locators/hashes above. `current.json` now records
`/root/r177_source_consumer_proof` as the frozen proof-handoff producer; the
proof worker is STOPPED. The reviewer was STOPPED after the 300s grant; elapsed
UNKNOWN, so full 300s charged. No tests, builds, probes, compiler/evaluator or
Yulang2 execution, Git, network, or scratch were used.

Final R178 accounting: 3000/3000 seconds charged, including the 240-second
closeout grant (elapsed UNKNOWN, so the full grant is charged); unused
conditional delta reserve 0 (it was consumed in the prospective delta review). **CLOSED_UNFINISHED_RESEARCH, CLEAN.** Parent, A/B,
source/native, implementation and production gates remain OPEN; no code slice
or probe is authorized.

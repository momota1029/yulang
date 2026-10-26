# Native replay lifecycle: actual owner equations and adversarial source audit

Date: 2026-10-26. Assignment `20261026-inference-native-replay-lifecycle-source`,
handoff revision 1. Worker `/root/native_replay_lifecycle_source`, generic
source/falsifier leaf. Requested specialist/model/effort and observed effective
model/effort: UNKNOWN. No descendants. This is a contribution to construction,
not independent review of the joint lifecycle packet.

Selected contract: `20261026-inference-source-boundary-next.md`, SHA-256
`a7e256cd39eeffe8901db6a087789a7ea676e2a5e555f1f533e5b55692711c54`.
Primary-reported starting baseline: `yulang3`,
`f7c7dcfc5cf2b55aedea5625470e81483d0561b8`. During this assignment the primary
reported publication of the accepted record-plan packet at
`b1a769800c609db77ed7ee5614af9906fd57ed0d`, with native inputs unchanged.
Neither report was independently checked with Git; this leaf has no Git grant.

## Outcome and unchanged parent

**Source-native evidence, with a concrete third-owner transport construction;
the complete lifecycle refinement remains unproved.** No genuinely unowned
native obligation or source-qualified compiler counterexample was established.
The proposed “no new replay at the third owner” counterexample is insufficient:
the prior descendant's physically retained bound is an actual carrier through
copy/transport, and later merged-row replay is a compensating execution path.

This audit constructs the exact key-level transport for an unchanged rigid
Function replay whose Value child changes representatives at a third owner.
It also establishes two useful simplifications from the bodies: merge witness
transport preserves the entire scoped flow, and local wrapper-context selection
is invariant under a row representative change. It distinguishes those facts
from the still-required induction over all constructor expansions, context
discharges, replay suppression, and return/cancellation.

The unchanged parent is `SourceProblem.InferenceSoundness`
(`Contracts.lean:128`), for every supported original source, original scope,
generated constraint and successful solution, yielding the original source
judgment and the same scoped witness. `NativeCorrespondence` remains a separate
application bridge. No restriction to scalar/identity-context traces, exact
records, or a pure Value fragment is adopted. The original source `j`, executable
record-boundary equation, full `completeCall`, contextual-effect meaning,
sharing, generalization and principality obligations remain unchanged.

## 1. Actual entrypoint and scheduling restriction

`constrain_live_item_with_inferred_entry` immediately selects
`run_candidate_typed_drain` when a candidate graph exists (`lib.rs:14001–14004`).
The apparent candidate settlement in the later legacy loop at `14044` is
therefore not a second reachable candidate scheduling route.

The reachable ordinary settlement owner is `step_typed_drain`, specifically
`Stage::Transport` with `current.is_none()` and an empty typed worklist
(`lib.rs:14308–14311`). Repository-wide symbol search found no other production
caller of `settle_candidate_intrusion`; `merge_candidate_rows` is private and
called only inside settlement (`candidate_intrusion.rs:568–595`).

Consequently, a proposed execution that inserts a merge halfway through this
same drain's Function/Tuple/Record/Variant Admission/Enqueue stages is not a
transcription of these bodies. Those stages admit/enqueue their complete sibling
list before returning to Transport. Actual difficult cases still exist:

* A popped replay child has finished local dispatch but its ack remains owned by
  the drain until Diagnostics and terminal acknowledgements.
* One settlement loop can merge several pending parent/copy pairs. An earlier
  merge queues children, and a later merge in that same loop changes their
  representatives before they are popped.
* Previously returned expansions persist in the erased derivation after their
  runtime operation has been reclaimed.
* A committed suspended drain retains partial local dispatch and ack state.
  Its allowed subsequent actions must follow its actual continuation owner;
  an arbitrary interleaved merge is not justified by suspension alone.

The full refinement should use these reachable scheduling facts rather than
quantifying over arbitrary combinations of native fields.

## 2. Correspondence table: fields, guards and transitions

All file references in this table are under `crates/yu-solver/src`.

| Event or guard | Actual owner | Required readback / transition |
| --- | --- | --- |
| Physical bound append | `candidate_extrusion.rs:702–875` | Canonicalize owner and bound; choose one of eight Value/Effect direct/exact lanes; append one addressed slot; read it back and require equality to `BoundKey(owner,polarity,bound)` before emitting evidence. Physical position and logical bound key are distinct. |
| Bound incidence attach | `candidate_context.rs:3283–3295` | If the same relation is already attached to this bound, do nothing. Otherwise append `(bound,relation,old_head)` and replace that bound's head. This is a persistent linked prefix, not a mutable list of endpoints. |
| Row comparison emission | `candidate_extrusion.rs:1115–1171` | Canonical reflexivity returns. For row/row, `level(upper) <= level(lower)` stores an upper on lower; otherwise it stores a lower on upper. Mixed row/rigid chooses the row owner. Both kinds then invoke ordinary replay. |
| Ordinary physical replay | `candidate_extrusion.rs:1070–1113` | Read direct then exact opposite slots; build ordered lower/upper BoundKeys; call `begin_replay(...,false)` and `drive_replay(...,None)`. This queues children without running them inside the enumeration. |
| FreshUse restoration replay | `candidate_extrusion.rs:966–1068` | Save count, retain owner/polarity/bound/emission/occurrence/cause, re-read the live canonical owner at the saved index, call `begin_replay(...,true)`, retain that operation, advance only after its actual completion/return. Existing complete-block temporal compensation is still needed. |
| Replay relation construction | `candidate_context.rs:4037–4050` | Context is identity iff both attached contexts are identity, otherwise `Replay(lower_context,upper_context)`; sources are their interned union; lower demand must be absent; flow is ordered transformer composition plus upper demand. Intern the complete key and retain the exact recipe. |
| Recorded-head suppression | `candidate_context.rs:4009–4031` | Ordinary replay enumerates new-lower/all-upper and old-lower/new-upper only. Incoming replay replaces both old heads with empty. The old/old disposition must come from actual earlier construction. |
| Dependency-key suppression | `candidate_context.rs:4050–4056` | After constructing the exact Replay recipe, ordinary mode suppresses only if the entire dependency, including child, both parents and both input BoundKeys, exists. Incoming mode bypasses this skip. Neither branch reads the completed map. |
| Operation reservation | `candidate_context.rs:4060–4068` | Store recorded heads, allocate the actual operation ID, retain raw task, input keys, heads, prior heads, incoming flag, child sequence, `queued=consumed=0`, Idle and not retired. Heads advance at generation/reservation, not at child return. |
| Queue ownership transfer | `lib.rs:15223–15243`; `candidate_context.rs:2384–2395` | Reserve evidence/queue/undo first. Require Idle, not retired, `index<len`, `consumed<=index<=queued`; increment queued only when `index=queued`, then perform infallible insertion. An already transferred initial item is not transferred twice. |
| Pop and ack retention | `lib.rs:14313–14334` | Reserve drain ack storage and replay-completion undo before pop; retain exact ack in the drain's ordered ack sequence and retain the current item. |
| Pending task transport | `candidate_context.rs:3767–3785` | Require canonical old relation pair = canonical task pair. If already exact, retain the relation; otherwise intern canonical pair with old post-check context, sources and scoped flow, add Derived, and return it. Raw task and old relation remain available. |
| Context execution | `candidate_context.rs:3800–3885` | Runs before pair memo suppression. Check canonical pair match and scoped-kind guards; observe scoped Effect operands; execute zero-word filters if present. Exact allowances are admitted/replayed before discharge and residual are recorded. |
| Pair currentness | `lib.rs:13507–13518` | Raw typed-pair memo must exist, and current processing relation must map to the exact current intrusion generation. Endpoint coincidence alone is insufficient. |
| Pair marking | `lib.rs:15295–15340`; `candidate_intrusion.rs:423–456` | At admission, store `completed[processing_relation]=generation` only for a canonical admitted key. This is before structured children finish. Save old map entry/memo state for rollback. |
| Local structured expansion | `lib.rs:14528–14869` | Preserve immutable term tags and all original indexes. Function has four ports; tuple indexes, record paired indexes/optional rules and variant alternative/payload indexes remain distinct. Admission precedes child completion. |
| Sibling admission/enqueue | `lib.rs:14955–15060` | Retain `children,next,pending`; admit the next reverse-indexed child into pending, enqueue pending at the front, then increment next. Returning to Transport waits for the entire sibling list. |
| Merge physical carriers | `candidate_intrusion.rs:599–708` | Resolve source/target representatives; skip identical reps; copy both sides while leaving source physical storage intact; transport each source fiber/origin; change forest and level/non-generic metadata; canonicalize all original incidence; increment generation; reopen diagnostic root; replay every target lower. |
| Parent/copy bound transport | `candidate_effect.rs:685–727` | Walk every executable incidence of the source BoundKey and retain a `ParentCopy` Transport with evidence. The separate origin table lacks origin-to-fiber association: its metadata admissions explicitly retain that gap and do not manufacture identity fibers. |
| All-owner canonicalization | `candidate_context.rs:4230–4254` | Freeze original `bound_keys.len()`, scan every original incidence including third owners, transport each changed key with `EqualityCanonicalization`, attach its fiber, and add Derived provenance. This does not itself enqueue all third-owner products. |
| Scoped transport | `candidate_context.rs:2867–2878,4318–4331` | Preserve old sources, use post-check context, and apply actual demand-root transport. For the actual merge witnesses this operation is identity on scoped flow; arbitrary Extrusion/FreshUse transport is not covered by that simplification. |
| Asynchronous queued result | `candidate_context.rs:4180–4228` | With no provenance, all children may be queued but not consumed; `Queued` means the outer drain still owns completion. It is not a return receipt. |
| Synchronous Running/Ready | `candidate_context.rs:4095–4153` | Running retains exact operation/index/drain, matching occurrence and cause. Ready requires `queued=consumed=index+1` and that the child frame has been popped. Delivered clears waiting to Idle; it does not acknowledge twice. |
| Ack and terminal return | `candidate_context.rs:2405–2451`; `lib.rs:14881–14945` | Preflight completion before side effects; complete only the exact next consumed index; perform Diagnostics, ordered acks, ReturnReady; validate destination Running ack/drain and exact cursor equality; retain Ready receipt before popping the top frame. |
| Commit and retirement | `candidate_context.rs:2190–2247`; `lib.rs:9498–9532` | Reclaim only retired Idle operations not retained by a live restoration. Preserve suspended work, reset terminal preflight state for a new journal, and discard undo after committed ownership transfer. Reclamation does not erase erased historical evidence. |
| Rollback and ID reuse | `candidate_context.rs:2076–2175`; `candidate_intrusion.rs:188–242`; `lib.rs:9646` onward | Restore old frames/cursors/retired flags, remove newly allocated operations, restore next ID, heads, incidence, dependencies, discharge state, representatives, generation and memo entries; outer route rollback restores physical rows and worklist. Cancel the entire attempt suffix, including mutations of preexisting owners. |

## 3. Exact constructive equations

Write `Cq` for the shallow current representative operation: it changes only
`ValueRow`/`EffectRow` endpoint IDs (`lib.rs:11839–11845,13491–13497`), not a
rigid term and not its descendant references. `key(r)` contains pair, context,
source-set identity and scoped-flow identity. Let `post(r)` be the actual
`post_check_context` at `candidate_context.rs:3297–3302`.

### Replay quadrants and exact dependency

For one input pair `(L,U)`, let `H` be current linked heads and `P` the recorded
heads. In ordinary mode the emitted *candidates* are exactly

```text
(H.lower \ P.lower) × H.upper
  ++ P.lower × (H.upper \ P.upper).
```

For each candidate `(l,u)`, the child key is

```text
pair    = Cq(task_pair(task))
context = I, if context(l)=context(u)=I;
          Replay(context(l),context(u)), otherwise
sources = union(sources(l),sources(u))
flow    = (compose(flow(l).transformer,flow(u).transformer), flow(u).demand)
guard   = flow(l).demand = None.
dependency = Replay(child,l,u,L,U).
```

Only exact ordinary dependency hits are removed from this candidate sequence.
For incoming use, replace `P` with empty and remove no dependency hit. This is
the exact source input to the reviewed `replay_quadrants_cover`; it does not
interpret old/old as returned.

### Actual merge witnesses preserve scoped flow

For an actual ParentCopy witness, the owner moves from a row to another row;
the bound endpoint is read canonically. For EqualityCanonicalization, both
endpoints are changed only by `Cq`. Thus an endpoint equal to
`NegativeFunction(demand.root)` remains the identical rigid endpoint. In the
`transported_scoped` loop either no endpoint matches that root or the loop
assigns that same root. Therefore, directly from these particular bodies:

```text
transported_scoped(r,w_merge) = scoped_flow(r).
key(transport(r,w_merge))
  = (Cq(bound_pair(w_merge.to)), post(r), sources(r), scoped_flow(r)).
```

This is a source calculation, not a checker-certified lemma. It covers both
row kinds and both actual merge reasons. It says nothing about a FreshUse or
structural Extrusion witness whose rigid demand root can change.

`candidate_context_source` depends only on whether the upper endpoint is a
specific rigid Allowance with a closed weight (`:3361–3372`), so

```text
local_context(Cq(pair)) = local_context(pair)
```

under a pure row representative change. Sources and scope transformer inputs
are not reconstructed from endpoints.

### A concrete third-owner Function-child square

Take a native prefix that actually admitted a Replay relation `r` with an
unchanged rigid positive/negative Function pair. Its actual Argument edge is

```text
FunctionPort { parent:r, child:a, field:Argument, operation:Swap },
pair(a) = (ValueRow(x), ValueRow(y)).
```

Suppose the actual row-emission branch has `level(x)<level(y)`. Then
`candidate_apply_value` emits `B=(ValueRow(y),Positive,ValueRow(x))`.
The successful Value child cannot have performed a nonempty zero-word filter
discharge: that branch rejects Value tasks (`:3831–3834`). Its emitted same-kind
bound fiber consequently has the same key as `a`, and interning identifies it
with `a` (ordinary bound flow preservation at `:3043–3060`, emission at
`:3895–3935`).

Now let a genuinely retained, qualifying extrusion parent cause `x` to merge
into `p`, with `y` distinct from both. The all-owner prefix scan visits the
actual incidence `(B,a,previous)` and constructs

```text
w = TransportWitness {
      from:(y,Positive,x), to:(y,Positive,p),
      reason:EqualityCanonicalization }
Transport { parent:a, child:a', use_origin:0, witness:Some(w) }
Derived { parent:a, child:a' }
attach((y,Positive,p),a').
```

The preceding equations calculate

```text
key(a') = (p <= y, context(a), sources(a), scoped_flow(a)).
```

This is exactly the key that a new Argument projection of the unchanged
Function parent `r` would produce: rigid children/indexes are unchanged;
`value_endpoint` reads row representatives; local context is unchanged;
the same Swap, source set, and Function demand projection are used
(`lib.rs:11753–11813,14800–14828`; `candidate_context.rs:3505–3567`).

There need not be a native `FunctionPort(r,a')` edge or a new replay operation
for `a'`. The actual carrier is the composed path

```text
r --FunctionPort(Argument,Swap)--> a --Transport(w)--> a',
```

ending in a retained materialized row constraint. Its existence is enough to
refute the alleged *absence of every owner* in this discriminator. It is not
enough to claim `a'` was newly dispatched or marked current. A valid ghost
expansion must retain the indexed old port followed by the real Transport;
requiring a direct replacement port edge would be the wrong readback equation.

For the opposite actual level branch, the stored bound is `(x,Negative,y)` and
the merging owner copy transfers it to `(p,Negative,y)`; the same normalization
gives `p<=y`. The storage orientation is allowed to differ from what a fresh
post-merge level comparison would select. The logical row constraint and its
provenance are what the transport must preserve.

If the third owner also had an upper `H`, the earlier product at `y` generated
`x<=H`; when that descendant materialized on `x`, the merge copies its upper
bound into `p` and replays the target product. If a row/row level choice stored
it at another owner, all-owner canonicalization transports that incidence.
This is the compensating route that an adversarial test must exhaust. This
paragraph is an induction step description, not a proof that every recursive
descendant graph is already closed.

## 4. Admission, suppression, discharge and cancellation discriminators

### Admission is earlier than local expansion and return

Function dispatch computes the child skeleton, calls pair admission at
`lib.rs:14830`, then installs `FunctionDispatch { children,next:0,pending:None }`
and `FunctionAdmission` at `14848–14849`. `mark_candidate_pair` has already
written the current generation. No Function child has yet passed the staged
port-admission/enqueue loop, let alone returned. Tuple/record/variant follow
the same admission-before-completion pattern. The raw completed map therefore
cannot read back an abstract “returned” set. This is a direct body-prefix
falsifier, not an arbitrary malformed state.

Within a generation, a duplicate may refer back to this admitted local
expansion. The erased object must retain that graph edge/cycle and the drain
or sibling cursor that still owns expansion. Replacing the duplicate with a
terminal proof loses an actual obligation.

### Two independent skip reasons, three old dispositions

| Situation | Actual disposition to retain |
| --- | --- |
| Old/old excluded by heads | A construction from the earlier successful begin-replay prefix, including its exact recipe and owner/expansion. Current generation is not tested. |
| Exact dependency hit | The dependency's prior creation, and the operation/child disposition produced by that creation. The hit says neither “current” nor “returned.” |
| Earlier merge queued child, later merge changes pair | The original queued item and ack; pop performs `candidate_context_transport_task` and canonical raw-Value alias enqueue. The queue item cannot be silently dropped. |
| Locally expanded but ack outstanding | The complete old child skeleton/materialized leaves and the drain's exact ack index. Native settlement does not certify the child as returned before the terminal stage. |
| Earlier operation returned/reclaimed | The erased historical expansion; transport its actual descendant carriers, including the third-owner square above. Operation-map absence alone proves no disposition. |

The whole `Dependency::Replay` is required. Swapping either input/parent or a
source set changes its evidence, even if endpoint pairs happen to coincide.

### Context discharge requires a graph square

Native transport uses `post(r)`, whereas rebuilding a Replay uses the attached
parent contexts. A universal literal equation
`Replay(context(l'),context(u')) = context(old_replay)` is not established and
is not the needed law.

The real discharge owner executes every extracted filter before recording
discharge (`candidate_context.rs:3827–3885`). Each filter owns an exact
Allowance upper bound. If already registered, the code still attaches this
occurrence's origin and replays that bound; otherwise it calls
`candidate_apply_effect`. Only afterward does it retain `discharged` and the
nonidentity residual, if any. Merge preserves/copies those physical allowance
bounds and their fibers. Newly introduced lower operands must meet them through
the actual merged-row product and any required subsequent row propagation.

The graph-transport equation therefore factors an old Effect query into
**its actual filter-bound obligations plus its residual expansion**, transports
both, and reconnects their exact sources and scoped flow. It must not identify
two ContextIds or use an assumed semantic equivalence of Allowance contexts.
Identity contexts, zero-word filter discharge and directed residuals remain
separate cases. The zero-word filter helper explicitly rejects a mix of replay
filters and directed residuals (`:3750–3754`).

### Cancellation suffix and numeric-ID reuse

An erased operation identity should be `(attempt_epoch,numeric_operation_id)`.
Existing committed operations keep their old identity through a resumed route.
New operations use that route's fresh epoch. Rollback restores the old state
of preexisting owners, removes all newly allocated operations/dependencies/
incidences, restores recorded heads and next numeric ID, and restores the
representative generation and memo markings. A later attempt can reuse the
numeric ID without inheriting the cancelled operation's proof.

“Discard only newly created graph nodes” is insufficient: the failed suffix
may have advanced or completed an older operation or popped its drain.
`typed_drain_undo` and `replay_operation_undo` restore those earlier owners.
The ghost inverse must do the same. A retained suffix from the cancelled epoch,
an ack with the wrong operation epoch/index, or a changed source set fails the
corresponding exact readback equation. Commit may preserve a suspended prefix;
its successful Rust return is not a closed inference return.

## 5. Full dispatch scope and first remaining equation

The body audit retains every dispatch family: Value bottom/top and diagnostic
terminals; canonical aliases; retained extrusion rewrites and recapture;
row application; all four Function ports; exact tuple indexes; exact paired
record indexes, missing optional fields, missing required diagnostics and
optional-to-required `RecordAdaptationUnavailable`; all matching variant
alternatives and payload positions; Effect reflexivity/bottom, Support member
and tail expansion, Contribution/AnnotationMember membership or allowance-tail
propagation, EmptyNegative mismatch, and actual context execution. The owning
Effect cases are `candidate_effect.rs:1237–1305`; sibling Effect tasks receive
their actual Derived relation through `enqueue_task`/`enqueue_item` and
`candidate_enqueue_evidence`, not a Function-port label.

No complete formal execution transcription or closed Lean root is supplied by
this leaf. The remaining precise construction is `MERGE-EXPANSION-COVER-1`:

```text
Given an actual earlier Replay D=(r,l,u,L,U), its actual expansion E,
and an actual successful parent/copy merge q with retained witnesses W,
construct the current expansion disposition of each suppressed obligation
from the transported graph E, the copied/materialized row leaves,
the actual context-filter registrations and residuals, and new merge products.
```

Its critical leaf instance is concrete. Let an old descendant Effect relation
`a` of the unchanged rigid replay `r` have executed filters `A_i`, retained
their upper-bound fibers `f_i` on an affected row `x`, and continued with
residual `post(a)`. For `x→p`, the actual witnesses are

```text
w_i : (x,Negative,Allowance(A_i)) -> (p,Negative,Allowance(A_i)),
reason ParentCopy(parent_index),
```

with any canonical third-owner descendant incidence using
`EqualityCanonicalization`. The required proof must connect each new lower
fiber at `p` to the exact transported `f_i` obligation and retain the residual
child disposition, even if the old rigid parent Replay is skipped and the
third owner is not re-enqueued. The copied bounds and witnesses are present;
the universally constructed finite expansion disposition for their resulting
old/new and suppressed descendant products is what is not proved here.

This is **not** a claimed missing native owner, unowned runtime obligation, or
source defect. The source provides plausible real carriers, including the
fully calculated Value/third-owner instance. The missing item is the complete
recursive graph-transport induction from those carriers to the coverage
consumer, with cycles and actual context discharge retained. A theorem taking
that conclusion as `CurrentTransport`, `Covered`, or “every skip is valid” would
not discharge this packet. The accepted structural row model cannot fill this
gap or absorb width/optional records; the accepted native record-plan and
boundary-query constructors retain their original scope.

The next in-scope proof step is to construct that graph disposition from the
transcribed execution, using the scheduling restriction in section 1 and the
explicit carriers above. If it fails, the falsifier must identify an actual
old `D`, exact witness, changed descendant incidence and missing disposition
after all compensating paths, followed by a genuinely generated source trace
before making a compiler-defect claim.

## 6. Frozen inputs, checks and cessation

SHA-256 of inspected bytes:

| Path | SHA-256 |
| --- | --- |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `rules/goal-driven-sprints.md` | `e50f5d4f79814c87af56e7dc34ddb6ab968abb523826c72ecdc40a8920397c0a` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/NativeReplayCoverage.lean` | `e65d925ab5222fd6bbc4bf63e756701aaba1273fff677ceb052d7f66e6450b7e` |
| `notes/theory/lean/YulangClosure/NativeRecordPlan.lean` | `3cf43fdb754748b83a6816791d640752dda491b87f7e2513a27548a950b27d43` |
| `notes/theory/lean/YulangClosure/BoundaryQueryClosure.lean` | `7dad22c1b94e404be5dc4aaa51203e8d3882fd4c61006eb8b0c5f6f87a30f727` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |

Read root operating maps, applicable proof/authority/top-level rules, the full
selected packet, current progress, the original root, accepted replay paper,
and actual native bodies. Reused the accepted quadrant and complete-block
coverage boundaries. Sent exact source equations and reachable-state
restrictions to `/root/native_replay_lifecycle` and the primary during work.
The primary supplied the discharge-factoring observation; the complete native
body was independently read here. This source contribution cannot independently
certify the combined construction.

Grant: 900 seconds, zero checkers/tests/probes. Consumed **zero** Lean, Cargo,
native test, executable-model, or compiler invocations; only reads, searches,
byte hashes and this sole write. No Git/status, imports, compiler/test edits,
semantic changes, central-state edits, or new runtime retention/checking
mechanism. The isolated scratch lease was unused. Sole new path is this file.

Outcome is ready for fresh nonauthor M3 review with the core producer's frozen
packet, not acceptance or whole-parent closure. Primary owns review assignment,
adjudication, publication and remaining-goal status. Writes stop after hashing
this revision. No descendants, background process or unresolved writer lease.

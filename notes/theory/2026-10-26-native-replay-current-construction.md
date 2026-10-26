# Replay current-disposition graph: constructed recursion and exact open frontier

Date: 2026-10-26. Status: kernel-checked local construction; independent review
pending; original inference and `MERGE-EXPANSION-COVER-1` remain OPEN.
Author: `/root/native_current_r3`, bounded generic leaf following
`.codex/agents/lean-prover.toml`; no claim of a custom-role runtime launch.
Baseline: `60e8684224a8a911a5627b845312750a192be777`, branch `yulang3`.

## 1. Original obligation and the actual advance

The unchanged original parent is `YulangClosure.SourceProblem.InferenceSoundness`
in `lean/YulangClosure/Contracts.lean`:

```text
∀ source scope constraints solution,
  supported source → generates source scope constraints → solves constraints solution →
  ∃ witness, sourceJudgment source scope witness ∧ sameScoped source scope witness solution.
```

The same source scope and one shared witness remain mandatory. Complete Call,
Function ports, source/event scopes, effects and hygiene, optional records,
method selection, generalization, lawful use and the original supported source
domain remain in that parent. Native success is separately related to generated
constraints and solutions by `SourceProblem.NativeCorrespondence`. Current
intrusion qualification is the immutable Value-birth-level induced graph rule,
not the superseded cross-level SCC criterion. No qualification or language
behavior is changed here.

The immediate task is the current expansion graph in
[Replay lifecycle §6](2026-10-26-native-replay-lifecycle.md). The previous
[merge construction](2026-10-26-native-merge-expansion-construction.md) supplied
installed filter/residual carriers, local Effect expansion transport and indexed
historical Replay origins. This continuation constructs a genuinely recursive
current graph for the **Effect operand and retained-bound part** of that task:

- Replay generation itself registers each emitted complete child key. Both
  old/old exclusion and whole-dependency suppression now lead to all finite
  depths of the same current graph, rather than stopping at a historical index.
- Local operand expansion registers every emitted child automatically. Existing
  retained, queued or active owners can be reused as back-references. No
  acyclic graph or recursively closed child premise is supplied.
- Each merge transports the whole graph invariant. It preserves queued work
  from earlier merges and every installed child edge, while moving each
  retained bound to its computed carrier and preserving its original-parent
  dependency path.
- When a requested closed expansion depth fails, the proof constructs a walk
  through actual installed child lists to one concrete retained, queued or
  active owner. The walk has fewer edges than the failed depth.

This is a partial reduction of the original gate, not its closure. The graph
still lacks the constructor that ties an entire nonidentity Context execution
to **all** of its installed checks and residual continuation, and lacks Value
constructor ports. Its event projection has not been authenticated against one
accepted native execution. The theorem does not infer accepted native return
from a graph label, a dependency key, Rust `Ok`, or an admission memo.

## 2. Finite graph and explicit construction events

The new module is
[`YulangClosure/NativeReplayCurrent.lean`](lean/YulangClosure/NativeReplayCurrent.lean).
Its sole project import is the frozen `NativeMergeExpansion` module, which
imports `NativeReplayCoverage`. The existing `NativeReplayAcknowledgement`
module was read as a consumer and source boundary; this result does not depend
on a changing execution-history artifact or modify any root import.

`Graph.vertices` is a finite list of complete original `Key` values. Only this
finite domain is observed in the status function. Every key keeps its rigid
endpoint identities, stored Context ID, optional source-set ID and complete
Effect transformer ID. `Graph.q` is the current representative map. It changes
the observed row endpoints, not the original key's opaque payload.

`Disposition` distinguishes `retained`, `queued`, `active`, `expanded body` and
`returned body`. An expanded body is one of:

1. a computed local return;
2. the entire emitted child-key list;
3. an exact retained bound fiber with a path from the original key.

A local return is the actual successful `checkOperand` return, or a reflexive
current pair with transformer zero. The reflexive alternative preserves the
native Context-stage rejection of a nonidentity scoped self-relation.
Conflicts and availability failure do not become local returns.

`Step` gives the finite event constructors. `Reachable` starts from an empty
Replay generator and graph, then applies these constructors:

| Event | Concrete graph action and guard |
| --- | --- |
| `lower`, `upper` | Execute the existing generator's actual per-bound attachment operation. |
| `replay` | Execute its actual incoming/ordinary product, including both ordinary skips, and register every newly emitted key. |
| `external` | Register successful creations from a different physical input pair in the same shared graph. It changes no heads for the selected pair. |
| `queue` | Move a registered retained owner to queued. |
| `activate` | Move a registered queued owner to active. |
| `localReturn`, `reflexive` | Install the corresponding computed local-return body for an active owner. |
| `children` | Install a complete list whose current endpoint projection equals the actual computed operand outcome, and register every child. |
| `bound` | Construct `exactFiber bound residualContext sources transformer`, attach it and a Derived path, and retain it for the active owner. |
| `returned` | Record an erased return marker for an already installed body. This event is not itself an acknowledgement proof. |
| `merge` | Run the previous concrete copy/canonicalization operations on fiber storage, add their actual transport edges, update representatives, and transport all bodies. |

`keyOf : Nat × Nat → Key` is fixed for one exact ordered pair of physical
BoundKeys and its two attached relation identities. This is the same fixed
constructor boundary as the preceding Replay origin proof. It is data, not an
assumed semantic coverage law. Authenticating it requires the whole native
Replay key construction, including stored contexts, unioned sources, ordered
scope-transformer composition and the upper demand. A new physical input pair
has its own generator; its creations enter the selected projection through
`external`. These projections must be obtained from the same native history.
They cannot choose unrelated favorable graphs or redefine `keyOf` mid-trace.

The graph may share one expansion owner between several Replay occurrences.
It deliberately does not identify their distinct `(birth, operation, index)`
acknowledgement obligations. In particular, registering a new occurrence of a
key with an earlier returned body does not acknowledge the new occurrence.
The `returned` label contributes the same local body to the graph invariant as
`expanded`; no public theorem concludes an actual runtime receipt from it.

## 3. Recursive currentness is derived, including after repeated merges

`Accounted` combines the generator's origin invariant, the graph invariant and
the connection from every historical batch member to a registered root.
`initial_accounted`, `step_accounted` and `reachable_accounted` derive this
structure from the explicit empty-start event history. Public roots take
`Reachable`; they do not take `Accounted`, recursive coverage, a valid completion
ledger, a semantic solution or assumed `LocalLaws`.

`CurrentAt tables graph depth key` is a separate depth-indexed consumer. At
positive depth it requires a registered current owner and one of:

- an explicitly retained, queued or active frontier;
- an exact current retained fiber and original-parent path;
- a computed local return;
- the whole current operand child list, with every child satisfying the
  preceding depth.

The proof of `invariant_all_depths` is induction on depth over the **same finite
graph**. It does not recurse down a topological ordering. A back-reference can
therefore revisit an existing owner. `register_active_backreference` shows
that registration preserves an active owner; it does not turn that owner into
a local or terminal return.

The principal root has the exact logical shape:

```lean
historical_child_current
  (h : Reachable tables keyOf s)
  (owner : s.replay.operations[operation]? = some batch)
  (child : batch[index]? = some pair) :
  ∀ depth, CurrentAt tables s.graph depth (keyOf pair)
```

`dependency_skip_current` derives this result for a pair in the retained
whole-dependency set and proves that ordinary generation skips it.
`old_old_current` derives the same result for the excluded old/old quadrant.
`fired_product_current` combines the actual quadrant computation with root
registration, covering every current product after ordinary or incoming Replay.
The historical positions remain erased creation positions, not runtime operation
IDs or acknowledgement receipts.

The merge induction requires the representative-forest equation
`∀ row, qNew (qOld row) = qNew row`. It derives whole current operand transport
from the existing exact `Effect.operand_expansion_transport` equation.
Child lists and graph vertices stay connected; they are not replaced by a
new full-product scheduler. `walk_merge` preserves every installed-edge walk,
including repeated visits. `merge_queued` preserves a queued owner through
another merge. No cycle becomes terminal merely because its representatives
change, and an outstanding acknowledgement is not completed by merge.

The algebraic merge rule can preserve the graph at more cuts than the native
scheduler permits. That stronger algebra is not evidence that those cuts are
native-reachable. The native erasure must use the actual Transport/current=None
and empty-worklist settlement boundary, including the case where an earlier
merge queued work before a later merge in the same settlement loop.

## 4. Exact payloads and retained-bound carriers

### Operand child construction

`concrete_operand_children` removes the need to supply a favorable arbitrary
child-key list. It takes the actual `checkOperand` output list, the native
representative idempotence equation, an active registered owner and raw
immutable admission tables. It computes every child key through `admittedChild`
and constructs the corresponding `Step.children`, reachable next state,
child payload equations and all-depth currentness of the parent.

This follows the actual `enqueue_task -> candidate_enqueue_evidence ->
candidate_context_admit -> relation` call chain. A child's Context is its
**child-local** `candidate_context_source`: for a closed Allowance, the interned
`PrefixLeft(weight,Identity)` ID; otherwise identity. The child inherits the
processing parent's source-set and entire scoped transformer. The parent's
stored Context and post-check residual are not substituted for that local
Context. `sourceContext_rename` proves that row canonicalization does not alter
this Allowance-based selection. Table/interner readback and validity of IDs
remain source authentication duties.

The generic `Step.children` is an erased record of the complete actual emitted
keys and its constructor equation. The concrete theorem constructs those keys
for this operand owner. It does not validate the earlier Context execution or
assert semantic meaning for arbitrary Context IDs.

### Bound continuation and successive generation changes

`row_residual_step` computes the native level-selected residual bound from
`residualBound`; it does not assume that a physical bound exists. It requires
an active registered row-lower request, its exact current pair, distinct
endpoints, native levels and the actual residual Context ID. Both row/row level
branches and a rigid upper keep the original directed comparison. General
`Step.bound` also retains an exact addressed bound with that comparison; its
source application must use the owning emission, not an arbitrary choice.

`BoundCurrent` requires actual membership in graph fiber storage, the exact
current endpoint pair, exact fiber endpoint keys, unchanged sources and
transformer, and a dependency path from the original full key. It intentionally
has no equality between the old stored Context and a new carrier Context.

At every merge, the body stores the newly computed carrier, so a later merge
starts from that carrier, not from a repeatedly reinterpreted ancient fiber.
The previous carrier theorem gives the exact Context formula at each step:

```text
if renameBound q oldFiber.bound = oldFiber.bound
then oldFiber.key.context
else post(oldFiber.key).
```

`bound_current_merge` combines physical copy selection, the frozen-prefix scan,
carrier membership, exact endpoint normalization, payload preservation and
path composition. It covers a residual stored at a third owner. Identity-context
Allowance fibers remain identity through the previously established publication
and carrier result; no universal stored/post-check Context equality is used.

## 5. Terminal reduction and its finite falsifier

`unfinished graph` is a computed finite filter of graph vertices whose state is
retained, queued or active. It includes more than the native worklist.
`ClosedAt` is the same finite-depth constructor unfolding with those three
frontier alternatives removed. It **still leaves concrete retained row fibers**
as obligations; its name does not mean semantic subtyping or a solved row model.

`historical_child_closed` proves all depths of `ClosedAt` from the same reachable
history, indexed historical child, and `unfinished graph = []`. This last
premise is explicit. The result does not derive it from an empty worklist,
operation-map erasure, `completed`, `discharged`, `ReplayDriveOutcome::Queued`,
Rust `Ok`, or a separately chosen cursor projection.

The stronger diagnostic reduction is:

```text
historical_child_closed_or_frontier:
  for every depth, either ClosedAt(depth, root), or
  ∃ last length,
    length < depth ∧ Walk(root,length,last) ∧ last ∈ unfinished(graph).
```

`Walk` follows actual installed expanded/returned child lists, and
`missing_depth_has_frontier` constructs that witness by induction on the failed
depth. This is an exact falsifier for the proposed closed graph projection. It
is not a source-qualified compiler counterexample. To eliminate it for an
accepted native drain, one must map the exhibited final owner to its actual
retained operation, worklist entry, active/pending dispatch slot, or already
installed local body, then use the actual terminal sequence on that same
execution. Independently valid cursor and frame histories do not suffice.

## 6. Native source owners and remaining correspondence

All source paths below are under `crates/yu-solver/src` at the frozen baseline.

| Component | Native owner and consumer | Proven here / exact remaining boundary |
| --- | --- | --- |
| Replay reservation and two skips | `candidate_context.rs:3992–4076` | Generator events construct roots and all-depth current graph coverage. Authenticate linked heads, complete dependency keys, operation creation epochs and fixed `keyOf`. |
| Queue transfer | `lib.rs:15223–15250`; `candidate_context.rs:2390–2410,4180–4228` | Queued graph owners survive registration/merge. Map physical occurrences and transfers; a shared key is not an ack identity. |
| Active owner and dispatch | `lib.rs:14288–14420` | Active roots/back-references remain explicit until a local body is installed. Authenticate current task, processing relation and partial child-enqueue ownership. |
| Local operand outcomes | `candidate_effect.rs:1237–1305` | Full indexed members, optional Support tail, Allowance tail and local-return equations feed recursive graph construction. Conflicts/unavailability are not accepted closure. |
| Reflexive return | `candidate_extrusion.rs:1147–1159`; `candidate_context.rs:3807–3811` | Equality return includes the zero-transformer guard. Context success remains separate. |
| Operand child payload | `lib.rs:15214–15230`; `candidate_effect.rs:513–519`; `candidate_context.rs:3025–3036,3361–3372,3456–3482` | Child-local Context and inherited sources/transformer are computed. Authenticate the concrete immutable table/interner projection. |
| Bound retention and placement | `candidate_extrusion.rs:1159–1180`; `candidate_context.rs:3898–3936` | A row-lower bound is constructed with actual residual Context, physical endpoints and Derived path. Full Context factoring and successful callback/replay association are not supplied. |
| Merge and carrier update | `candidate_intrusion.rs:568–708`; `candidate_context.rs:4230–4254,4318–4331` | Graph invariant, queued states, paths and all finite depths survive concrete carrier operations. Authenticate source copy inputs, prefix, representative forest and post-check map in one history. |
| Admission guard | `candidate_intrusion.rs:423–456`; `lib.rs:13507–13518,14830–14849` | No theorem reads `completed` as child completion. An actual duplicate must map to the proper existing graph expansion owner. |
| Ack and actual return | `candidate_context.rs:2369–2462`; `lib.rs:14881–14947` | Existing ordered cursor/terminal proofs remain available. The new graph's erased return marker does not prove their joint readback or accepted diagnostic state. |

The graph is erased proof data. It neither proposes a runtime metadata change
nor establishes an efficient compiler implementation of graph construction.
Failed/rolled-back events must be erased at the same committed checkpoint as
all native owner mutations. This module has no rollback constructor; it must be
composed with a common transaction history, preserving birth identities under
numeric reuse. No dependency on the concurrent execution-history lane is used.

## 7. Application back to the unchanged parent

This construction discharges the recursive **operand-subgraph** step left after
authenticating generation, emitted keys and local retained bounds. The previous
historical Replay origin can now be consumed by `historical_child_current`;
a suppression is not left with just an old batch witness. The same generated
child lists form the finite graph used at every depth and after every merge.
The finite path theorem identifies the exact unresolved owner if terminal
frontier elimination cannot be established.

The first remaining application work for `MERGE-EXPANSION-COVER-1` is still
substantial and concrete:

1. Construct the outgoing graph clause for the **entire actual Context
   factorization**: every installed Allowance check plus the exact residual or
   consumed-endpoint branch. Merely choosing one valid retained fiber for a
   full-context parent is insufficient. Use the preceding installed-filter
   carrier/path theorems; retain the parser's pure-Replay versus directed
   residual distinction and all successful callbacks.
2. Extend the same graph with all actual indexed Value ports, source record
   adaptation and remaining constructor branches. An Effect-fragment result
   does not remove these cases from the original supported language.
3. Derive one native event erasure that shares all maps, queues, frames,
   generations and transactions. Associate each Replay occurrence and duplicate
   admission with its graph owner; validate the actual merge cuts, including
   earlier queued merge work and pending acknowledgements.
4. At actual accepted return, eliminate the relevant unfinished-owner witnesses
   through that shared execution and ordered diagnostics/ack/ReturnReady events.
   Then supply semantic row/fiber closure, Context interpretation and the
   original source-scoped inference connection. No full solution or shared
   source witness is constructed by `ClosedAt` alone.

These are retained A/B correctness obligations, with construction-owner readback
also exposing reconstruction debt. They are not reclassified as optional
all-model characterizations. No original theorem is weakened, no supported
source is excluded, and no source-qualified impossibility or compiler defect
is claimed. The primary owns further assignment, independent review, status,
Git integration and production decisions.

## 8. Verification and frozen evidence

The fixed native executables were
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake` and its
sibling Lean. Lake reports `5.0.0-src+eb6cafb (Lean version 4.35.0)`; Lean reports
`4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The distribution digest
was provisioned/verified by the primary; this leaf performed version checks
and records executable hashes in its manifest.

All proof checks used the independent project
`/workspace/scratch/f98087c7ac1a/native-current-r3/project`, copied exact project
inputs, its own `.lake`, `LEAN_NUM_THREADS=1`, `lean -j1 -M1024`, `lake --no-cache`
and a 120-second whole-check deadline. No dependency, manifest, shared cache,
root import or compiler code was modified. No network, Cargo/native probe,
installation or Git operation ran.

Eleven focused checker calls were used, within the fourteen-call allowance.
Call 01 preserved the sandboxed Lake configuration-detection failure; subsequent
calls used the authorized process environment with the same fixed toolchain.
Material proof failures remain in calls 02–05, 07 and 09 with exact failed source
snapshots. They concern dependent-induction arguments, simplifier-closed goals,
existential list annotations, constructor-pattern arity, explicit event/type
parameters, an unavailable tactic spelling and the reserved binder `local`.
They were repaired without removing claimed cases or adding proof axioms.
Calls 06 and 08 checked coherent earlier roots. Calls 10 and 11 checked the final
source plus the full originating-module audit. Call 11's total measured time was
3.155 seconds; child CPU was 2.477 user + 0.641 system seconds, and observed child
maximum RSS was 1,000,944 KiB. No resource-limit increase was used.

The final audit visits all originating constants, including private/generated
declarations, prints each theorem's exact type and full transitive axiom set,
and rejects every project axiom/nonstandard dependency. It audited **143 theorem
constants among 333 declarations**:

| Complete axiom set | Theorem count |
| --- | ---: |
| None | 72 |
| `propext` | 35 |
| `propext`, `Quot.sound` | 34 |
| `propext`, `Classical.choice`, `Quot.sound` | 2 |

The two classical theorems are the finite failure-path extraction and its
historical-child alternative. The main constructive graph/Replay roots use
`propext, Quot.sound`. No `sorryAx`, project axiom, native-evaluation assumption
or checker bypass occurs. A changed/dependency-cone source search found only
the legitimate native API name `candidate_context_admit` in a comment.
This is kernel/checker evidence, not native correspondence or independent review.

The scratch manifest records all 29 governing/source/configuration inputs,
exact project dependencies, source snapshots, logs, commands/exits and audit
outputs. Full per-theorem types/axioms are in `theorem-inventory.json` and the
origin census log. The companion handoff and `freeze.json` record final output
hashes and writer-stop status. The primary must assign a fresh independent
reviewer to these exact bytes before promoting the result.

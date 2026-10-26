# Native replay lifecycle: construction stopped at expansion transport

Date: 2026-10-26. Status: source-grounded proof frontier; complete lifecycle
refinement UNPROVED; fresh independent review pending.

Author: `/root/native_replay_lifecycle`, bounded generic `lean_prover`/`prover`
fallback. Concrete native equations were contributed by
`/root/native_replay_lifecycle_source` and the primary. Neither contributor is
an independent reviewer of this result. No Lean module is supplied by this
packet, and no compiler defect or impossibility theorem is claimed.

## 1. Result and unchanged original obligation

The attempted construction reaches a specific missing induction step:
**transport the actual finite expansion of an earlier Replay across a
parent/copy merge, including the Effect checks emitted before discharge and
the exact residual continuation, and use that transported graph for suppressed
current products.** The native source supplies concrete carriers for those
checks and continuations. This investigation has not constructed the complete
graph from them.

Several stronger proposed readback equations are unsuitable. The native
`completed` map is written at pair admission, before constructor children
finish. A transported child need not receive a replacement direct FunctionPort
edge, a newly queued Replay, or a new current-generation memo entry. A change
from a relation's original context to its recorded post-check residual need
not preserve its RelationKey. None of these differences establishes a lost
obligation. The exact third-owner construction in section 5 gives a positive
native carrier and rules out the simplest alleged missing-owner argument.

The unchanged parent is
`YulangClosure.SourceProblem.InferenceSoundness`, defined at
[`Contracts.lean`](lean/YulangClosure/Contracts.lean):128:

```text
∀ source scope constraints solution,
  supported(source) → generates(source,scope,constraints) →
  solves(constraints,solution) →
  ∃ witness, sourceJudgment(source,scope,witness) ∧
             sameScoped(source,scope,witness,solution).
```

The original supported domain, shared witness, scopes, generalization,
Function/Call behavior, effects, optional records and method selection remain
unchanged. `SourceProblem.NativeCorrespondence` is a separate bridge from
actual native success. An operational graph, if constructed, would supply
one native input to that bridge. It would not supply the original record
adaptation equation, semantic context interpretation or complete Call
certificate.

The selected contract is
[`20261026-inference-source-boundary-next.md`](../../tasks/agent-loop/inbox/20261026-inference-source-boundary-next.md),
revision 1, SHA-256
`a7e256cd39eeffe8901db6a087789a7ea676e2a5e555f1f533e5b55692711c54`.
The source contribution is frozen separately in
[`20261026-inference-native-replay-lifecycle-source.md`](../../tasks/agent-loop/inbox/20261026-inference-native-replay-lifecycle-source.md),
revision 1, SHA-256
`90367a823a99dd891ea7e5053508017384b9f3d787571821a60076934971d780`.
Its all-event table and full source audit are inputs to this paper, not an
independent certification of it.

## 2. Attempted execution refinement and its exact owners

The intended producer starts from the actual initial state and a finite
committed native execution ending at accepted outer return. It must construct
an erased finite obligation graph over the same raw tasks, canonical bounds,
relation keys, ordered Replay antecedents, constructor indices, occurrence,
cause, queue items and drain owners. Cycles may refer to an already active
node. They may not replace that node's unfinished expansion by a terminal
proof.

The induction needs the following distinct dispositions. These names describe
the intended proof object; they do not assert that the native structs already
contain a semantic certificate.

| Disposition | Actual native readback |
| --- | --- |
| Retained/reserved | `ReplayOperation.children`, `inputs`, `heads`, `prior`, `incoming_use`, and its creation event; or a retained bound incidence awaiting the owning enumeration. |
| Queued | Exact `TypedWorkItem` and `ReplayChildAck(operation,index)` in the worklist; `queued` has advanced, `consumed` need not have. |
| Active | `TypedDrainFrame.current`, its stage and original task/relation, or the exact `pending` item and `next` cursor in a structured dispatch. |
| Locally expanded | Actual child list/port incidences and emitted bound/check obligations; descendants can still be queued or active, and the parent's ack can remain outstanding. |
| Returned | Diagnostics and the ordered acknowledgement sequence have completed; ReturnReady publishes the exact destination receipt before the top frame is popped. |
| Cancelled | Rollback removes the attempt's new objects and restores mutations of earlier owners. Cancelled events cannot support a later reused numeric operation ID. |

The corresponding native bodies are `candidate_context.rs:33–145` for the
retained fields, `lib.rs:14288–14420` for the stage machine,
`candidate_context.rs:2369–2462` for transfer/preparation/ack/return, and
`lib.rs:14881–14947` for terminal drain publication. All native file references
in this paper are under `crates/yu-solver/src`.

An asynchronous `drive_replay(...,None)` can return `Queued` with children
still owned by the outer worklist (`candidate_context.rs:4180–4228`). A
synchronous child retains its exact Running/Ready ack and drain index. Neither
operation-map absence nor Rust `Ok` supplies an accepted outer return. The
required accepted result includes the relevant error state, empty worklist,
settled intrusion, completed diagnostics and exact drain/ack return. Existing
`finish_candidate` packages observations after its field-tail check; it is not
a final semantic model checker (`lib.rs:10681–10693`).

### Admission is not completion

`record_typed_pair_admission` calls `mark_candidate_pair` at
`lib.rs:15340`. For a canonical admitted key, that stores
`completed[processing_relation] = generation`
(`candidate_intrusion.rs:423–456`). Function dispatch calls admission before
installing `FunctionDispatch { children, next:0, pending:None }`
(`lib.rs:14830–14849`). At this exact source prefix no staged Function child
has yet been admitted/enqueued, much less returned. Tuple, record and variant
dispatch have the same ordering.

`pair_is_current` also requires raw memo presence and the actual processing
relation's current generation (`lib.rs:13507–13518`). It is an admission and
recursion guard. Identifying this table with `NativeReplayCoverage.Owner.completed`
fails at an ordinary structured-admission prefix. The intended ghost graph
instead retains the local expansion owner and any active back-reference.

### Actual merge timing restricts the induction

The candidate path at `lib.rs:14001–14004` immediately selects
`run_candidate_typed_drain`; its later legacy-loop settlement is not another
reachable candidate route. The operative settlement occurs only at
`Stage::Transport`, with `current=None` and an empty worklist
(`lib.rs:14308–14311`). `merge_candidate_rows` is private and is called by
settlement (`candidate_intrusion.rs:568–595`).

Therefore the proof cannot posit an arbitrary merge halfway through this
same drain's Function/Tuple/Record/Variant admission sequence. Real cases still
include locally expanded children awaiting terminal acknowledgements and
children queued by an earlier merge in the same settlement loop before a later
merge changes their representatives. Suspension must follow its actual
continuation owner; it does not license arbitrary interleaving.

## 3. Both replay skips and the coverage consumer

For actual lower/upper BoundKeys `L,U`, write their current linked incidence
lists as `newLower ++ oldLower` and `newUpper ++ oldUpper`, where the split is
the saved `replay_heads[(L,U)]`. `candidate_context_begin_replay`
(`candidate_context.rs:3992–4076`) enumerates exactly

```text
newLower × (newUpper ++ oldUpper) ++ oldLower × newUpper.
```

The checked
`YulangClosure.NativeReplayCoverage.replay_quadrants_cover` states that this
delta together with `oldLower × oldUpper` is the full current product. It does
not assert any disposition for the old/old part. Incoming FreshUse sets both
old heads to empty and bypasses ordinary dependency suppression;
`incoming_replay_covers_all` supplies the product identity in that case.

For every enumerated fiber pair `l,u`, the native child is interned from:

```text
pair    = canonical(task_pair(task))
context = I if context(l)=I and context(u)=I,
          Replay(context(l),context(u)) otherwise
sources = union(sources(l),sources(u))
flow    = (compose(flow(l).transformer,flow(u).transformer), flow(u).demand)
guard   = flow(l).demand = None.
```

The exact dependency is `Replay(child,l,u,L,U)`. Ordinary mode then skips an
already present whole dependency at `:4054`; incoming mode does not. This
second skip is independent of the recorded-head exclusion. Neither consults
the current-generation memo or the return state.

For a same-generation dependency hit, an induction on actual dependency
creation can refer to the prior creation event and its retained operation or
historical expansion. That reasoning must survive rollback and retirement.
For a generation change, it additionally requires section 6's expansion
transport. Naming the prior dependency alone does not prove that transport.

The accepted abstract scheduler's `.merge` enqueues a literal full product.
Native merge copies both sides, canonicalizes all bound incidences, advances
generation and visits each target lower (`candidate_intrusion.rs:599–708`),
but those visits still use the two skips. There is no asserted step equality
between these implementations. A successful source-faithful incremental proof
would use the quadrant theorem and derive an exact owner or transported
expansion for each skipped pair; only then would it supply the same product
coverage consumer. That derivation is still absent here.

## 4. Constructive reductions from the native equations

These are calculations from the frozen bodies, not new kernel-checked
theorems. They reduce the difficult transport equation without adding a
semantic law.

### Representative pullback retains the exact child skeleton

Let `q` be the old representative map and `q'` the map after a same-kind
parent/copy merge. Merging roots and path compression retain the old
equivalences, so the required row calculation is `q'(q(x)) = q'(x)`.
`canonical_value`/`canonical_effect` change only row endpoints, while
`value_endpoint`/`effect_endpoint` reread row children through the current
representative map (`lib.rs:11753–11845,13491–13497`). Rigid term handles and
their immutable constructor data do not change under this operation.

Thus the exact current child endpoints are obtained by applying `q'` to the
old child endpoints. The constructor labels are retained as follows:

| Constructor | Exact native child identities retained |
| --- | --- |
| Function | Argument: upper argument to lower argument; ArgumentEffect: upper AE to lower AE; ResultEffect: lower RE to upper RE; Result: lower result to upper result. The four port tags and Swap/Preserve operations stay distinct. |
| Tuple | Original tuple index and matched pair after exact arity validation. |
| Record | First matching lower label, original lower/upper indices, target order, optional absence, missing-required diagnostic and optional-to-required availability failure. |
| Variant | Every matching negative alternative with the same tag/arity and each original lower-index, upper-index and payload-index triple. |

The record branch is the exact width/optional scan represented by the accepted
`NativeRecordPlan`; it is not `Regular.recordPairs`. A diagnostic branch can
return availability success without becoming an accepted comparison. Source
boundary identity and executable record adaptation remain later obligations.

### Merge transport preserves all scoped-flow fields

For the actual `ParentCopy` and `EqualityCanonicalization` witnesses,
owners move only between same-kind rows and bound endpoints are canonicalized
only at rows. `transported_scoped` (`candidate_context.rs:2867–2878`) can
change a demand root only when a witness endpoint equals the rigid
`NegativeFunction(demand.root)`. Such an endpoint is unchanged by these merge
witnesses. The loop either does not match or assigns the identical root.

Consequently actual merge transport preserves the entire `ScopedFlow`,
including transformer, original Call, use instance, negative Function root,
output scope and input route, as well as the source-set identity. This
calculation does not extend to Extrusion or FreshUse witnesses, which can
change rigid demand roots and have their own constructors.

`candidate_context_source` depends only on an upper rigid Allowance and its
closed weight (`candidate_context.rs:3361–3372`). A row merge leaves that
selection unchanged. Function-port demand projection likewise retains its
actual root check and the same AE stamp / RE protect construction at
`:3505–3567`. No scope or source data are reconstructed from equal endpoints.

The remaining difference is explicit:

```text
key(transport(parent,w_merge))
  = (canonical(bound_pair(w_merge.to)),
     post_check_context(parent), sources(parent), scoped_flow(parent)).
```

It uses that exact parent's discharge state, not a globally interchangeable
context. All-owner canonicalization separately records a Derived edge after
the Transport operation (`:4230–4254`). These are retained proof paths, not a
replacement direct constructor-port event.

## 5. The third-owner case has a real carrier

Consider an actual earlier Function Replay relation `r` and its Argument
incidence

```text
FunctionPort(parent=r,child=a,field=Argument,operation=Swap),
pair(a) = ValueRow(x) <= ValueRow(y).
```

Use the actual branch `level(x)<level(y)`. `candidate_apply_value` stores the
lower bound `B=(y,Positive,x)` at owner `y`
(`candidate_extrusion.rs:1115–1149`). A successfully executed Value child
cannot have a nonempty filter discharge, because that consumer requires an
Effect task (`candidate_context.rs:3831–3834`). Its ordinary bound emission
retains its context, sources and flow, and interns the same relation `a`.

Now an actual qualifying parent/copy occurrence merges `x` into `p`, with
`y` distinct from both. The frozen all-owner incidence scan includes `(B,a)`
and constructs exactly

```text
w = TransportWitness(from=(y,Positive,x),to=(y,Positive,p),
                     reason=EqualityCanonicalization)
Transport(parent=a,child=a',use_origin=0,witness=Some(w))
Derived(parent=a,child=a')
attach((y,Positive,p),a').
```

Section 4 calculates

```text
key(a') = (p <= y,context(a),sources(a),scoped_flow(a)).
```

This is the key that a newly projected Argument child of the unchanged rigid
Function pair would have. The native carrier is the old indexed FunctionPort
followed by the actual Transport. It is unnecessary to invent
`FunctionPort(r,a')`, assert that `a'` was newly dispatched, or reinterpret a
memo entry as current completion.

The other level branch stores `(x,Negative,y)`; the merge copies the owning
row's physical bound and transports its origins to `(p,Negative,y)`.
Both normalize to the same required directed comparison. A fresh post-merge
level comparison may select a different storage side; literal storage-event
equality is not the intended refinement.

If `y` had an upper `H`, the earlier product emitted `x<=H`. A materialized
upper at `x` is copied to `p`; if the level branch stored that comparison at
another owner, whole-prefix canonicalization transports its incidence there.
The merged target's replay then handles newly combined physical products.
These are concrete compensating paths. Proving all their recursive
descendants closed is the remaining induction, not a consequence of this
single square.

This example fixes the actual owner, old relation, changed child, witness and
retained disposition by the source equations. It is a conditional local
construction over a native prefix with those events, not a claim that this
paper generated a source program or executed such a trace. No new native probe
ran, and no compiler-defect claim follows from this calculation.

## 6. First unproved equation: discharged Effect expansion transport

### What is reused and what is new

The local factorization is already established in
[`2026-10-21-r181-contextual-cut-consumer.md`](2026-10-21-r181-contextual-cut-consumer.md),
section 4: processing a nonidentity filter relation retains its installed
Allowance obligations and exact residual; `discharged` is not semantic
satisfaction or child completion. That result explicitly leaves generation
changes and canonical transport to their actual witness/history. Repeating
its unchanged-representation argument would not remove this packet's premise.

The new reductions here identify the merge timing, the exact third-owner
carrier, full scoped-flow invariance for actual merge witnesses, and the
preserved indexed structural skeleton. They leave a narrower, concrete graph
composition task than endpoint currentness: transport the already factored
Effect expansion and reconnect every affected product to it.

### Exact local instance at the frontier

Fix an actual earlier dependency

```text
D = Replay(child=r,lower=l,upper=u,lower_input=L,upper_input=U)
```

and an actual descendant Effect relation `a` in its expansion. Suppose the
real Context step on `a` extracted filters `A_1,...,A_n`, with lower operand
`EffectRow(x)`. For every filter, before publishing discharge, the native
consumer does one of these operations (`candidate_context.rs:3840–3875`):

* reattach this occurrence's origin to an existing exact upper
  `(x,Negative,Allowance(A_i))` and replay it; or
* call `candidate_apply_effect(x,Allowance(A_i))`, which installs and replays
  that bound.

Call the actual attached filter fiber `f_i`. Its checked-bound construction
uses identity context but retains a Derived link to the full parent `a`, its
sources and its Effect scoped payload (`:3904–3935`). After those calls the
executor records `discharged(a)` and its exact residual `R=post(a)`. If the
upper endpoint was not consumed, Dispatch continues with that residual and
its actual row/operand obligations.

For an actual merge `x→p`, source-side bounds and origins are copied before the
forest change. The filter carriers have actual witnesses

```text
w_i = TransportWitness(
  from=(x,Negative,Allowance(A_i)),
  to=(p,Negative,Allowance(A_i)),
  reason=ParentCopy(parent_index)).
```

They produce attached `f_i'` with the same source set and scoped flow. Their
Allowance view IDs stay rigid. Any affected residual bound stored at a third
owner has its own `EqualityCanonicalization` witness from the frozen prefix.
These witnesses and fibers are present in the source construction. There is
no assertion that their owner is absent.

Now let `h` be an exact lower fiber at `p` after copying and canonicalization.
The target-row enumeration visits its physical pair with every retained
Allowance upper. The required child for `(h,f_i')` has the native key

```text
pair    = canonical(lower_endpoint(h)) <= Allowance(A_i)
context = native_Replay_context(context(h),context(f_i'))
sources = union(sources(h),sources(f_i'))
flow    = (compose(flow(h).transformer,flow(f_i').transformer),
           flow(f_i').demand)
```

and exact input BoundKeys and ordered parents. New candidates obtain actual
operation/child owners. Old/old exclusion and exact dependency hits instead
need the historical expansion and its transported descendant disposition.
Neither skip manufactures that disposition.

The unproved step is to **construct**, from this actual earlier expansion,
these actual witnesses, the new merge products and the actual discharge
events, one finite graph in which every such child and the residual
continuation has its exact current disposition. It must cover repeated
suppression, row cycles, Support-member and Allowance-tail children, structured
ports farther along the graph, and preexisting owners whose acknowledgements
are still pending. This is `MERGE-EXPANSION-COVER-1`.

The old and new root labels need not be literally equal. Replay reads the
attached fibers' stored contexts, while transport uses each parent's
`post_check_context`. A valid construction must factor the emitted checks and
residual and retain their original dependencies. It cannot posit a universal
context equality or replace the square by semantic Allowance preservation.
The parser at `candidate_context.rs:3670–3765` retains the distinction between
identity, pure Replay filters, and payload-free directed residuals; mixed
Replay filters and directed residuals are rejected. Successful handling of one
case does not establish the others.

### Why the available quotient results do not close it

`SimpleSub.Store.quotient_pullback` and `History.quotient_sound` in
`SimpleSubConstraintSyntax.lean` / `SimpleSubConstraintSoundness.lean` pull a
supplied solution back through an exact renamed constraint store/history.
They do not construct this native expansion or its owners.
`SimpleSubRegularConstraintSoundness.GraphRenaming` requires a concrete graph
lookup equation and its accepted-result consumer still takes a checked target
certificate. It also uses its represented structural record relation. Supplying
one of those conclusions as the input to this native graph step would retain
the missing premise and would not handle the original width/optional queries.

The accepted `BoundaryQueryClosure` and `NativeRecordPlan` remain available
consumers/components at their represented boundaries. Their query records and
indexed holes do not prove that a skipped native obligation reached an exact
returned or transported owner. No source `j`, contextual semantic law or full
Call certificate is inferred from their finite construction.

This is an unfinished proof obligation. It is not a refutation, a proven
impossibility, or a source-qualified counterexample. The source supplies
plausible carriers and this packet did not find a genuinely unowned obligation
after all compensating paths. Per the contract, construction stops here rather
than introducing a ledger with an assumed skip/transport law.

## 7. Return, rollback and complete dispatch remain in scope

The exact return discipline is necessary after section 6, not a replacement
for it. Completion requires the prepared exact ack, `consumed=ack.index` when
it advances, and the terminal Running destination with
`consumed=queued=ack.index+1` before Ready is published. The caller's prepared
ack/frame state is essential; `complete_replay_child` in isolation does not
recheck every earlier preparation guard. A separate primary-authorized
acknowledgement construction owns that component; no result from its changing
files is assumed in this frozen paper.

Rollback restores old frames, replay cursors, retired flags, heads, relations,
dependencies, incidences, discharge state and next operation ID
(`candidate_context.rs:2076–2175`), plus representatives/generation/memo state
(`candidate_intrusion.rs:188–242`) and physical/worklist journals. Erased
identity must distinguish a fresh attempt epoch from a reused numeric ID.
Cancelling only new nodes is insufficient because the failed suffix may also
have advanced or popped an older owner. Commit can reclaim a retired Idle
operation while an erased derivation retains its event; suspended active work
remains owned. These facts belong in the complete history induction.

The following full dispatch cases were inspected and remain obligations of
that induction:

| Family | Actual owner and retained distinction |
| --- | --- |
| Value terminals | Canonical alias enqueue; incompatible-shape diagnostics; bottom/top; ordinary equal/scalar behavior. `lib.rs:14460–14528`, `candidate_extrusion.rs:1115–1149`. |
| Value row/extrusion | Retained extrusion rewrite and recapture, new level-aware extrusion, exact rewritten relation and enqueue; row-bound placement and replay. `lib.rs:14471–14491,14706–14800`. |
| Function | Four typed ports, exact demand authentication/projection, reverse admission plus front enqueue. `lib.rs:14800–14869,14955–14981`; `candidate_context.rs:3505–3567`. |
| Tuple/record/variant | Exact original indices and target/matching order; optional cases, diagnostic and availability outcomes stay distinct. `lib.rs:14528–14705,14984–15060`; `candidate_context.rs:3572–3664`. |
| Effect row/bottom | Canonical reflexivity, level-directed row storage, bottom terminal. `candidate_extrusion.rs:1151–1171`; `candidate_effect.rs:1237–1244`. |
| Effect Support | All indexed AnnotationMember children and optional canonical tail; actual Derived admission through enqueue. `candidate_effect.rs:1245–1269`. |
| Effect member/Allowance | Allowed-member return, canonical tail continuation or retained mismatch; EmptyNegative mismatch; unsupported shapes return availability failure. `candidate_effect.rs:1270–1305`. |
| Context | Exact scoped observation/guards; validated zero-word filters, owned allowance checks and residual; memo handling occurs afterward. `candidate_context.rs:3670–3885`. |

No scalar-only, identity-context, all-local or exact-record fragment is
advertised as the original closure theorem. Existing complete-block
restoration and FreshUse results retain their original premises; repeating
the known live-index shift is neither new progress nor a defect claim.

## 8. Verification, parent application and freeze

The repository `yulang-lean-proofs` source/claim workflow was applied: original
parent definitions, selected authority, full contract, existing theorem types,
accepted coverage boundary and actual native bodies were read before choosing
the stop point. The current birth-level qualification supersedes historical
cross-level examples; no arbitrary row equality was promoted to an actual
qualifying source occurrence.

The selected native hashes and accepted Lean dependency hashes were rechecked
and match the contract. Complete identities and the sole output hashes are in
the companion handoff. There were **zero Lean/Lake calls, zero Cargo/native
tests and zero executable probes**. No new Lean declaration, theorem type,
axiom inventory or checker success is claimed; the corresponding new-module
audit is not applicable because no `NativeReplayLifecycle.lean` was created.
There are no failed checker logs to omit. No compiler source, imports,
dependencies, semantics, tests, shared status or Git state were written.

Parent application: the intended native coverage consumer is unchanged and
still cannot be instantiated without `MERGE-EXPANSION-COVER-1` and the complete
execution/readback induction. This paper removes several incorrect candidate
readbacks and records genuine transport carriers; it does not remove the whole
old-work disposition/currentness premise. The parent remains OPEN.

Fresh review should challenge the exact admission prefix, both skip reasons,
third-owner transport and compensation, the Effect factorization, and rollback
of mutations to preexisting owners. It must distinguish the conditional local
calculations from a generated-source trace and from a complete theorem. Any
compiler-defect claim would additionally require an authentic generated source
execution and exhaustion of all compensating paths. No runtime repair is
authorized by this frontier.

The primary owns the remaining graph-construction assignment, independent
review, shared status and integration. These two leased research outputs are
frozen at handoff; no scratch build, background process or descendant exists.

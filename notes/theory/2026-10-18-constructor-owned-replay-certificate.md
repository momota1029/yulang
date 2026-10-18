# Constructor-owned FreshUse and Replay certificate

Status: candidate static source correspondence and conditional local mathematics;
fresh independent review NOT RUN. Author `/root/constructor_replay_proof`,
sole writer, descendants 0. Requested Sol/high; observed model/effort
UNKNOWN/UNKNOWN. Sprint `npair-constructor-owned-replay-certificate-20261018`
rev1, contract SHA `67c7ed9cb896a46300fbf3852111e569af321b3d64ddf948b41c4ec30cd05bac`.
Supplied baseline `7087de449`, current checkpoint `a6e97a035`, neither
Git-inspected by this leaf. Source hashes below pin the actual inspected bytes.

## Parent and result

Original parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` stays OPEN,
original conditions closed **0 -> 0**. Preserve the same original contribution
`c` fixed before observation; complete declaration/reference/joint theta,
Sigma-Lambda/xi and provider/witness/residual dependencies; all original
providers, assignments, worlds, contexts, occurrences, typed positions, guards,
continuations, interactions, Call demands and futures. F1 and FK1 remain
independent. Adopted NPAIR §§2–4 and its adoption receipt govern; P3 requires
all reached contributions and alternatives, P4 the complete dependent
presentation through capture/generalization/extrusion and qualifying Value-SCC
intrusion. A diagnostic demand tuple is not `At(D,c,delta)`.

The actual advance is a constructor-selection lemma: a successful incoming-use
Replay enumeration over an exact restored upper fiber visits its FreshUse
relation as upper, so the correct local join is available by constructor
identity under the conditions below. No general p1→h ancestry is inferred.
The existing candidate verifier instead passes Replay child q as the copied
FreshUse child. This is unsupported for a whole Function comparison and can
be structurally impossible. Shared-conclusion reasoning is sound only after
actual RelationId equality, and does not supply a missing path to h.

## Coordinates and owning tables

All coordinates refer to one live State and one retained route. Cross-State,
rollback-retired and out-of-range addresses reject. Retain a tagged route
`Module(j)` versus `Local(j)`; these indices are different namespaces.
`instantiate_candidate_graph` stores `FreshRoute` and `commit_local_use` stores
`LocalFreshRoute`; their retained maps own `context_use`, `terms`, rows,
`effect_operands`, `scope_remap`, `scoped_relations`, `context_remap` and
`evidence_remap`. A tuple search does not select a route or authenticate a map.

Let `b` be the actual graph bound, `p=b.relation`, `S` its complete captured
snapshot, `a` its imported snapshot ID, `u` the nonzero context-use, `B` its
canonical destination BoundKey, and `p1` the actual FreshUse Transport child.
Keep selected Replay `e=(l,h,q,L,H)` and consumer C separate. `pair` denotes
the retained typed pair; `flow` the retained transformer/demand. Numeric IDs
for **both** first and second uses remain **NOT_OBSERVED** for every coordinate:
source call/seed/p, route/u/b/S/a, B/p1/admission/emission/slot, l/h/q/L/H/recipe,
C and its four children. No earlier single-use numeric row is transferable.

| Stage | Exact owner and retained evidence | Required equation/check |
| --- | --- | --- |
| Source Call seed | `candidate_context_seed`, source Call/introduction, occurrence slot 0 | D0=(k,0,t0,s0,InputRouteId(k)), t0=introduction.demand; actual origin/seed or actual traced descendant at p |
| Capture | `Capture::bound`, graph.bounds and graph.bound_evidence | b contains p and full source_bound; S retains relation, source_bound, both prefix heads and coverage |
| Map/import | `prepare_candidate_fresh_use` | a=evidence_remap[b.evidence], snapshots[a]=S exactly; all five Function term entries and owned scope/input maps |
| FreshUse relation | `begin_candidate_fresh_bound`, `candidate_context_fresh_transport_scoped` | actual Transport(p,p1,u,Some(from=b.source_bound,to=B,FreshUse)); attach(B,p1) |
| Admission | `candidate_bound_origin_with_evidence`, `candidate_context_reuse_fresh_relation`, evidence.admit | exact B, Some(p1), FreshUse{a,u,b.source_bound,Some(p1)}; snapshot/Transport checks |
| Physical slot | `candidate_insert_bound_with_evidence`, evidence_emit | emission names that admission and B; slot owner/lane/index addresses actual stored item |
| Fiber | State.attach / bound_relations | p1 belongs to exact B by the bounds head/bound_keys chain, beyond pair equality |
| Restore/Replay selection | `candidate_step_bound_restoration_child`, `candidate_context_begin_replay` | exact L/H from inserted/existing BoundKeys, actual cursor entries l/h; recipe and dependency name q |
| Consumer | Replay queue / typed drain / `candidate_context_transport_task` / Function dispatch | actual retained relation C processing whole Function pair, q=C or explicit checked q→C edges |
| Ports | `lib.rs` Function children, `candidate_step_function_dispatch`, `candidate_function_port_admit` | exact field, typed pair, operation, parent C, child flow and transformer |

Capture does not assume every graph bound has a relation: it explicitly emits
an absent-relation case. This certificate rejects that case. Snapshot equality
uses the saved prefix, not recomputed current group heads. Import does not
repair coverage. Processing/ordinary-seed gaps and
`ReplayUseAntecedentsNotRetained` remain explicit; a retained ReplayRecipe
also carries that latter gap.

## Constructor equations and physical contents

Write `canon` for the owning canonicalization and `intern` for
State.relation_with_scoped. Its full key is
`K=(pair,context,sources,scoped-flow-id)`; flow IDs intern the complete
ScopedFlow. Equal pairs/roots/tuples alone do not imply equal keys or IDs.
In one live consistent State, equal full keys intern to one relation ID.

`prepare_candidate_fresh_use` reconstructs Function nodes by their four child
indices; with source root t0 and j=negative_functions[t0],
`t1=terms[j]=Fun-(terms[ja],terms[jae],terms[jre],terms[jr])`.
Its mapped demand preserves k, maps s/i using the retained maps, sets root=t1,
and changes use to u only when the old input is owned by scope_remap.inputs.
Borrowed inputs retain the old use; they are not silently accepted as local.
The same maps remap the entire transformer support. For this bounded identity
case require source and mapped transformers 0 and root/typed-upper consistency.

The actual fresh relation is

```
B = canon(owner, b.side, item)  # endpoints reconstructed by kind and side
p1 = intern(canon(bound_pair(B)), context_remap[context(p)],
            sources(p), mapped_flow[p])
Transport = {parent:p, child:p1, use_origin:u,
             witness:Some{from:b.source_bound,to:B,reason:FreshUse}}
```

Positive-side owner is reconstructed upper; negative-side owner is lower.
Effect operands use retained.effect_operands where present, rather than an
invented Value conversion. The FreshUse constructor attaches p1 before physical
admission. Reuse checks exactly the imported snapshot's source relation,
source_bound, nonzero use, destination pair and actual Transport dependency.
Require pair(p)=bound_pair(source_bound) and pair(p1)=canon(bound_pair(B));
a postcanonical root mismatch still rejects. FreshUse needs its own evidence;
it does not emit a general FiberTransform merely because other transports do.

Physical insertion accepts only a canonical ValueRow or EffectRow owner.
It sets slot.index to the chosen vector's old length, pushes the item, then
emits the admission/slot link. Verify the currently addressed content as well
as emission metadata:

| Lane | Actual vector at slot.owner | Content equals |
| --- | --- | --- |
| ValueLowerRow | bounds[i].direct_lower_rows | ValueRow index of B.item |
| ValueUpperRow | bounds[i].direct_upper_rows | ValueRow index of B.item |
| ValueLowerAtom | bounds[i].exact_non_variable_lowers | full B.item Value endpoint |
| ValueUpperAtom | bounds[i].exact_non_variable_uppers | full B.item Value endpoint |
| EffectLowerRow | effect_bounds[i].direct_lower_rows | EffectRow index of B.item |
| EffectUpperRow | effect_bounds[i].direct_upper_rows | EffectRow index of B.item |
| EffectLowerAtom | effect_bounds[i].exact_non_variable_lowers | full B.item Effect endpoint |
| EffectUpperAtom | effect_bounds[i].exact_non_variable_uppers | full B.item Effect endpoint |

Positive side selects Lower, negative side Upper; Row versus Atom follows
actual reconstructed item kind. Require index in range and correct row owner,
kind and full polarity. Bounds membership is independently checked by
`bound_relations(B)`, which follows `bounds[B]` through actual bound_keys
entries. Slot content does not prove relation membership, nor the converse.

For `candidate_context_begin_replay(L,H,task,incoming_use)`, each enumerated
pair l∈fiber(L), h∈fiber(H) creates

```
ctx = identity if ctx(l)=ctx(h)=identity else ContextExpr::Replay(ctx(l),ctx(h))
flow(q) = { transformer: flow(l).transformer then flow(h).transformer,
            demand: flow(h).demand }
q = intern(canon(task_pair(task)), ctx, union_sources(l,h), flow(q))
e = Replay{child:q,lower:l,upper:h,lower_input:L,upper_input:H}
recipe_keys[e] -> recipes[id].dependency = e
```

The lower demand must be None or construction fails. Full L/H share the actual
row owner, with Positive/Negative sides respectively, and task is ordered
`L.item <: H.item`. Verify both fiber memberships and relation endpoint pairs
rather than the observer's pair-match booleans alone. For the identity subset,
require both input and resulting transformers 0, not one empty-state evaluation.

## Input identity lemma and shared-conclusion alternative

**Input identity lemma (candidate source-constructor argument).** Fix one
successful restore iteration from `begin_candidate_fresh_bound`, with mapped
relation p1 and an actual negative Value bound B. Assume the iteration reaches
`candidate_context_begin_replay` successfully; its re-read canonical inserted
BoundKey is exactly B; p1 remains in that exact live upper fiber; and an
actual opposite lower fiber member l is present at the captured heads. Then
that invocation retains a Replay dependency and recipe with upper **h=p1**.

Proof: `candidate_step_bound_restoration_child` orders `(existing,inserted)`
as `(L,H)` when side is Negative, so H=B. It passes incoming_use=true. Begin
Replay therefore sets old=(None,None); its first loop enumerates every lower
cursor entry from heads.0 to None against every upper cursor entry from
heads.1 to None. Actual attach(B,p1) put p1 in that enumerated upper chain.
Thus (l,p1) is visited. The constructor computes q, retains recipe(e), and
publishes dependency(e), also for an already existing incoming-use dependency.
Deduplication of RelationKey does not erase the retained dependency. This
is existence for the particular successful invocation/snapshot, not a claim
that an arbitrary observed Replay row used p1. If there is no opposite fiber,
no completed invocation, changed canonical B, retired membership, lower demand,
resource failure or root mismatch, the corresponding premise remains absent.
The code's saved physical opposite count and later live-index/canonical reread
make the exact invocation check necessary; graph-level endpoint matching cannot
replace it. Positive-side restored bounds select lower, and do not give this
demand-from-upper conclusion.

This establishes a concrete extraction strategy: start at the authentic route
and mapped Transport p1, then select the Replay dependency whose **actual upper
ID** is p1 and H=B. Preserve that selected e and authenticate its lower/recipe/
consumer. Do not pick by equal demand tuple. Alternatively, if selection begins
at a Replay row, check h=p1 or its actual checked path and reject a foreign row.
No generic p1→h path is emitted merely by restoring a bound; other constructors
can emit Derived/Transport edges, which must be separately retained and checked.

**Shared conclusion lemma (conditional).** Suppose the same actual q is both
an independently authenticated FreshUse Transport child and Replay child, with
all complete constructor keys, maps, imported snapshot, physical admission,
fiber memberships and recipe checked. Then q has both construction incidences,
and its stored demand equals the mapped FreshUse demand and the upper demand.
Proof is substitution into the two constructors and equality of their actual
child IDs/full keys. Multiple incoming constructors do not contradict that
local result; incoming-edge counts cannot refute it. This proves no p1→h path,
no transport of all dependent evidence from the FreshUse child to h, and no
fixed-c contribution association. If independent semantic derivations are
needed, retain them as separate derivations rather than merge their witnesses.

For the direct Function consumer fixture, shared conclusion cannot repair the
old p1=q requirement: physical B has a row owner. If B.side=Negative, pair(p1)
has lower=ValueRow; if Positive, upper=ValueRow. A whole Function comparison q
has lower=PositiveFunction and upper=NegativeFunction. Those enum alternatives
are unequal, so pair(p1)≠pair(q), hence p1≠q. This is conditional only on q
actually being that whole Function pair, and is a static endpoint contradiction,
not an observed numeric fixture result. Row-task Replay may have different
shape and must be judged using its full keys. The input-identity lemma is the
appropriate route for the direct Function case.

## Consumer and all four scoped ports

Replay retains a task with q and its ordered pair. The actual queue item,
transport/canonicalization, rewrite and drain owners determine C. Direct q=C
requires RelationId equality. Otherwise use explicit actual Derived/Transport
steps, checking pair and flow/root equations at every edge. Transport_task can
canonicalize endpoints while retaining flow; it does not by itself repair a
stale demand root. Function admission checks upper=root, so stale roots reject.
No tuple search or successful shape match establishes dispatch/execution.

At C require actual pair PositiveFunction(F)<:NegativeFunction(G), demand
D=(k,u,G,s,i), zero transformer, and both actual Function term views. The
`lib.rs` child array gives the following exact equations, admitted in reverse
array order by the drain but reconciled by field:

| Field | Typed child pair | Operation | Child demand; complete transformer |
| --- | --- | --- | --- |
| Argument | value(G.a,+) <: value(F.a,-) | Swap | None; identity |
| ArgumentEffect | effect(G.ae,+) <: effect(F.ae,-) | Swap | None; stamp_input(i) |
| ResultEffect | effect(F.re,+) <: effect(G.re,-) | Preserve | None; protect_body(s,i) |
| Result | value(F.r,+) <: value(G.r,-) | Preserve | None; identity |

`candidate_function_port_admit` uses context.processing as actual parent C,
requires zero parent transformer, validates NegativeFunction(root), consumes
the demand, interns each real child pair and records FunctionPort(C,child,
field,operation). Check all four actual child ScopedFlows. ScopeTransformer
structural equality supplies the full operation: stamp_input has stamped=[i],
scopes=[]; protect_body has stamped=[], scopes=[(s,keep_initial=true,
add=Missing([i]))]. Identity has both vectors empty. One evaluation at empty
inputs cannot establish these equations. An auxiliary Derived edge emitted
alongside FunctionPort is compatible and is not competing demand ancestry.
Retained admissions are evidence of construction; later effect execution or
accepted output needs its own runtime receipt.

## First missing evidence, reuse and parent application

The first missing concrete record is the authentic route's actual p1 Transport
child joined to its selected Replay **upper** h and H=B, with destination slot
content/membership checked. Owner: `begin_candidate_fresh_bound` and State
Transport/attach, then `candidate_step_bound_restoration_child` /
`candidate_context_begin_replay`. The current authenticator instead requests
`fresh_use_witness(p,row.child,...)` in candidate_scheme and supplies copied=q
to `authenticate_replay_ancestry`; this source code does not establish the join.
The existing root equality assertion does not establish h=p1. Both concrete
fixture rows, q→C and complete child equations remain NOT_OBSERVED.

Reuse prior CLEAN proof `2026-10-18-replay-fiber-consumer-certificate.md` only
under its real two-spine/snapshot/physical/consumer premises, plus prior
constructor theorem and conditional ancestry criterion at their pinned hashes.
The closeout's BLOCKING/MAJOR review is evidence of the old verifier's defects;
its tests never ran. Reject p1=q by argument, root equality as relation identity,
sibling use as ancestry, port lookup under h, unique incoming-edge counts,
tuple-first source selection and history's single-use IDs as this experiment.
No solver operation or ordinary source case is weakened.

Apply the input-identity lemma to local P3/P4: it identifies the exact producer
that can supply the previously assumed p1→h base case through constructor
selection. It removes a need to invent/reconstruct that path for a completed
negative-bound restore invocation satisfying the enumerated premises. It does
not prove either fixture success or transport `At(D,c,delta)`: the same original
c, full dependent provider/witness/residual presentation, all future lowers and
alternative routes remain with Operation/Call and capture/generalization/
extrusion/qualifying-intrusion/effect-consumer owners. Original fixed-c,
P3/P4, N-Transport, P5, F1/FK1, complete Call, soundness, principality,
termination and production stay OPEN. Shared conclusion supplies no stronger
parent application.

TODO `NPAIR-CONSTRUCTOR-UPPER-JOIN-20261018`: after fresh map review CLEAN,
Luna's leased implementation owner should expose actual p1 independently of q,
join exact Replay h=p1/H=B (or actual supported path), authenticate all physical
slot contents and full fibers, recipe, C and four child flows. Positive control
and each actual-record mutation must be independent: snapshot, addressed slot
content, selected fiber member, dependency kind, port endpoint, child flow.
Falsifier: a direct whole Function row requires p1=q; actual p1 not found in H;
wrong source snapshot/slot/fiber/recipe/port/flow still authenticates; a sibling
map substitutes; or either normal source route has no constructor-selected
Replay/consumer. This is a provisional evidence TODO inside the granted lease,
not permission for new storage, semantics or production promotion.

TODO `NPAIR-P3P4-DEPENDENT-TRANSPORT` persists: establish original fixed-c/At at
its accepted negative incidence, then prove complete dependent preservation on
all ordinary paths. Falsifier: omitted future/alternative, conflated residual or
provider/witness, permission-as-inflow, or one local frame action used for F1/FK1.

## Freeze and direct dependencies

Checks: bounded static source/authority reads and exact SHA-256 equality of
prior proof/contract/authority pins. Some combined reads truncated; decisive
symbols were reread in bounded excerpts. No Cargo, tests, solver execution,
Git, production edits, external contact, nested CLI, descendants or scratch.
All numerical runtime observations remain NOT_OBSERVED. This author cannot
independently certify this result or the combined implementation. Early fresh
map review belongs to Luna; stop condition reached after freeze.

Dependency authors: prior fiber proof `/root/replay_fiber_consumer_proof`;
prior ancestry `/root/replay_ancestry_proof`; constructor theorem `/root/demand_transport_proof`;
NPAIR source proposal `/root/negative_formal_pair_proposal`; adoption and
workflow authority Luna/user. Compiler author identities UNKNOWN; this leaf
claims no dependency authorship. Implementation handoff referenced by Luna at
SHA `fd8d0cedf660d023573084b5b2f12903ea998822e83962805352cc020555d473`
is a primary receipt, not a proof dependency used to derive these equations.

| Direct dependency path | SHA-256 |
| --- | --- |
| `tasks/agent-loop/sprints/npair-constructor-owned-replay-certificate-20261018.md` | `67c7ed9cb896a46300fbf3852111e569af321b3d64ddf948b41c4ec30cd05bac` |
| `notes/theory/2026-10-18-replay-fiber-consumer-certificate.md` | `691a537b441bff0947b47886f423199e9558740778d81e50858eedd85e3e3614` |
| `notes/progress/2026-10-18-replay-fiber-consumer-closeout.md` | `de28e8fe67aa858edab9f00314d6c8ec15af227e6fbc57b7a13e8529717ba524` |
| `tasks/agent-loop/inbox/20261018-replay-fiber-consumer-impl.md` | `813ee225d3f7515cd1611424995d3d857a4a2227fcd58a75ccb2763becd75e4f` |
| `notes/theory/2026-10-18-demand-root-transport-correspondence.md` | `426b1bf969eb9628b73f5bcddec38b2f169d41341479dda4019965b34fad1244` |
| `notes/theory/2026-10-18-replay-ancestry-authentication.md` | `00603a98b9f66eb71c61c0fe80e8812ff059c6cde54abd2d91e02036674381f6` |
| `notes/design/2026-10-17-negative-formal-pair-formation-proposal.md` | `0a73aaf7016e86dd5babbdd5482b05a793764418bc003607207ef0375ee46006` |
| `notes/design/2026-10-17-source-formation-proposals-adoption.md` | `d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `crates/yu-solver/src/candidate_context.rs` | `c0952a2c618bc01d7291f8c48c5e2012cffaa1c95491e2d026ff16a0831e0d12` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9e548da9575d74a1da9ca8e70a70249eb3dc7a7c0f54f2cba5c525e0bfe1e73e` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `2c535e0906a9cf6221fa4746ae815dc45ce18cf37f19a8e811f996d8422b7f6b` |
| `crates/yu-solver/src/candidate_effect.rs` | `9ea9498692bdff12c2a7ebd8546ca2b443a095c0700f3e87ad6c956cc690e212` |
| `crates/yu-solver/src/candidate_scope.rs` | `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a` |
| `crates/yu-solver/src/lib.rs` | `ddd1395877d4a76e27a1dcf32af90c6fcb0e58c739610a0115c03955628350e1` |
| `crates/yu-solver/src/tests/candidate_graph_call.rs` | `5ab72a8afcfb439e076f00d304909c0cc790c706687738389054fa590b578548` |
| `crates/yu-solver/examples/research_scoped_formal_replay.rs` | `e4c1bec2a41accfe09f664d5992b2575ce78b855c3ff622f08eeb6de8765e3d3` |

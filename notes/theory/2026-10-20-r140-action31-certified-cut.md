# R140 action31: replay read closure and the unresolved source cut

Status: **CANDIDATE/CONDITIONAL SOURCE DERIVATION; UNFINISHED/OPEN**.
The conditional certified-cut outcome has not been established for the fixed
source. In particular this is not R72 outcome A, B or C, a reviewed theorem,
or production authority. Sole author: `/root/r140_action31_proof`; no coauthors
or descendants. Requested model/effort: `gpt-6-sol` / high. Observed effective
model/effort: UNKNOWN; no runtime metadata was supplied to this leaf.

Contract: `tasks/agent-loop/sprints/action31-certified-cut-20261020-r140-rev2.md`,
revision 2, SHA-256
`7b59e9b448ed7e03859ab1777652ae4d8efacc001a363305ea654698a9243bb9`.
Baseline supplied by Luna: `7a584032e`. This leaf used no Git. Baseline-tree
validation is Luna's activation receipt in the contract; all 39 inherited live
dependency pins were independently matched at entry and again at freeze.

## 1. Parent and the exact application

The parent remains computation-forwarding preservation §§1, 6–7 in
`2026-10-15-computation-forwarding-preservation.md`: one shared satisfying
assignment, original current-formal identities and whole Name arguments, every
finite prefix, repeated calls, simultaneous receiving entries and independent
foreign-continuation obligations. Its source theorem is distinct from the
native mapped-admission premise and actual receiving/read/Force suppliers.
Simple-sub A/B, inference/evaluator correspondence and production remain OPEN.
R50 remains NOT ADOPTED. No local replay result discharges a foreign-continuation
quantifier.

The fixed ordinary source is exactly R138's `outer/loop/direct/helper` specimen.
Its action31 is the loop Lambda, with provider

```text
F_L = Function+(Int-, t_x-, R_L+, V_L+).
direct family: F_L <= D_d* -> (X <= Int-, n_d* <= t_x,
                              R_L <= C_d*, V_L <= U_d*).
helper family: F_L <= D_h* -> (Y <= Int-, n <= t_x,
                              R_L <= C, V_L <= U).
```

Stars denote actual retained copies, not their original rows. These are
separate demand terms and separate replay input keys. They are not a schedule,
a count of physical slots, or a list of all RelationIds. A later canonical
alias may alter the dispatched raw tuple. The provider Argument is Int-, not
X- or Y-. `admit_lambda_fact` first allocates R_L and completely drains slot4
`e[4] <= R_L`; Computation slot3 is absent; only then does slot2 admit F_L.
Thus even the state immediately before provider insertion includes slot4's
complete effect replay and acknowledgements.

The results below apply to the parent's mapped-admission supplier as follows.
They replace an endpoint-only reconstruction of the two families with exact
local source formulas for their physical/fiber selection, currentness and
merge sweeps. They do not supply the actual input state at action31, hence do
not establish the parent's required mapped bounds or a later production
`Work::Bound` and independent consumer. The missing supplier is named in §7.

## 2. What is reused

The reused R138 derivation is authored by `/root/r138_proof`, with separate
Luna owner-map work. Its fresh compiler/source and spec/authority reviews
accepted partial research only. Earlier R73 authors `/root/r73_astra` and
`/root/r73_researcher` retain their historical provenance; this leaf does not
claim their unfinished suffix or its unreviewed statements as a proof.

R138's reviewed partial source prefix is reused for its actual scope: 17
expression identities, 44 source actions, the helper capture/restoration and
successful Local publication boundary, its restricted two-group/pending
ledger, and the action27 Result fragment. R138 does not establish the complete
action27 effect descendants, action31 state, boundary1 capture, later production
copy, or independent consumer. R73 remains unreviewed/unfinished; its budget
overrun and incomplete ledger grant no premise here.

In particular R138 supplies generation4 and consumed pending vector [3,4,5,6]
before action25, not generation4 for every later time. It supplies an authentic
action27 duplicate Result slot and two replay dependencies, not all action27
slots. Its identity-context/default-ScopedFlow constructor argument is reused
only for this fixed ordinary source. Sources, providers, residuals, transports,
emissions and witnesses remain distinct even under equal RelationIds.

## 3. Exact local replay generator and frame lemma

Owners: `candidate_extrusion.rs:867` (`candidate_replay_bound`),
`:674`/`:699` (physical opposite selection),
`candidate_context.rs:3767` (`candidate_context_begin_replay`),
`:3136`/`:3155` (fiber cursor and attachment), and
`lib.rs:11593`/`:12460`/`:12801` (currentness, dispatch, Function ports).

Fix one actual invocation of `candidate_replay_bound(owner,+,F_L,parent)`.
It canonicalizes owner and F_L, snapshots the opposite count, and visits the
physical direct-upper-row vector followed by the physical upper-atom vector,
each in increasing index. Each physical slot is retained independently,
including equal items. The item is canonicalized when read. For each slot the
ordered inputs are

```text
B+ = (canonical(owner), Positive, canonical(F_L))
B- = (canonical(owner), Negative, canonical(actual slot item)).
```

There is no deduplication of the physical loop. A direct-family or helper-family
atom can therefore be selected more than once. Such repetitions need not emit
the same children, since previous iterations can change saved replay heads.

For ONE `candidate_context_begin_replay(B+,B-,task,false)`, let L and U be the
newest-first linked fiber lists at B+ and B-, and let l0/u0 be their recorded
old heads, absent heads being None. The emitted ordered candidate products are

```text
(new lower prefix L..l0) x (all U), then
(old lower suffix l0..None) x (new upper prefix U..u0).
```

The outer loop is lower-first and the inner loop upper-first. The first
quadrant owns new/new. For each product (l,u), the actual source constructor
forms the canonical task pair, ordered Replay context (IDENTITY in this
source), exact source-set union, composed ScopedFlow, and interns the whole
RelationKey. It records an evidence recipe BEFORE testing whether the exact
`Dependency::Replay{child,l,u,B+,B-}` was already present. An ordinary replay
pushes the child only when that dependency was absent. Distinct dependencies
may push the SAME child RelationId. Incoming-use replay sets old=(None,None)
and bypasses this ordinary dependency suppression; it is not this invocation.
The recorded heads are advanced after generation, before child completion.

**Local frame lemma (conditional on explicit inputs, candidate proof).** Two
states give the same ordered candidate products, child RelationIds and Replay
dependencies for this one generator invocation if they agree on:

1. the task and ordered BoundKeys, canonical endpoint map, actual head IDs and
   every visited `(RelationId,next)` link, including old-head stop positions;
2. each visited relation's full key, source-set contents and scoped payload;
3. relation/context/source/scope interner lookup results and allocation
   frontiers for every key generated in the preceding order;
4. exact Replay dependency membership and evidence recipe state consulted by
   those products, dependency edge/bundle propagation state, the
   replay-operation counter and retained storage;
5. the same sequence of successful fallible reservations, arithmetic/resource
   checks and accounting observations.

Proof: the two nested loops have identical starts/stops. Induct on their
lexicographic cursor positions. Equal relation payloads yield equal keys and
source/scoped products; equal interners/frontiers yield equal child identity.
Equal dependency membership chooses the same suppression branch. Keep the
evidence-recipe mutation even on the suppressed branch. Advance equal heads;
allocate the same operation with the same child vector, queued=consumed=0,
retired=false and Idle wait. This is finite for this saved list traversal.
Nothing in this proof asserts that the required values have been generated by
the fixed source, or that downstream drains terminate.

For the physical selection loop an analogous induction additionally retains
the complete selected opposite vectors and canonicalization paths at each
iteration. Retaining only a set of items fails because physical iteration and
saved-head mutation are ordered. This applies separately to both families;
it does not identify the lists at their two different B- keys.

Currentness is a separate dependency. At each actual Dispatch it is exactly

```text
typed_pairs.contains(raw task key)
AND processing_relation exists
AND completed[processing_relation] == intrusion.generation.
```

Raw aliases first retain their own memo/diagnostic edge and enqueue canonical
work. Only canonical admission records relation completion. Two relations on
one endpoint pair can therefore append two equal physical slots. A current
child can suppress an append while its separate operation acknowledgement
still remains required. Function-port admissions occur Result, RE, AE,
Argument; front insertion makes Argument the next popped port, with its
descendants before the following queued port. A family is not four atomic
simultaneous transitions.

## 4. Sweep-aware frame lemma: the nonlocal read is real

Owners: `candidate_intrusion.rs:568`/`:601` (`settle_candidate_intrusion`,
`merge_candidate_rows`) and `candidate_context.rs:4005`/`:4091`
(`candidate_context_canonicalize_bounds`, transport with evidence).

If pending_cursor==pending.len(), settlement clears dirty and returns without
compression or merging. Otherwise it compresses forests and consumes pending
parents in vector order. A nontrivial merge appends BOTH physical sides of the
copy to its parent, preserves copy storage, redirects the representative,
updates minimum level/non_generic and capture incidence, and then invokes the
global context sweep BEFORE assigning the next equality generation. It then
reopens the root when applicable and replays every physical lower of the
merged parent. The equality-generation frontier is not a replay-child frontier.

For each sweep let N be `context.bound_keys.len()` at invocation entry. Its
loop visits EXACTLY indices 0..N, in order. At index i it reads raw key k_i,
parent relation p_i and canonicalizes k_i's owner and item. If to_i==k_i,
that iteration emits no transport. Otherwise, in order, it:

1. snapshots `(k_i,Some(p_i))`, interns that evidence snapshot, obtains the
   transported scope and the parent's post-check context/sources;
2. interns the canonical relation, records a Transport dependency and evidence
   transform, and attaches the relation at to_i unless already on that fiber;
3. interns the canonical pair relation again with the actual post-check scope
   and records the separate Derived dependency.

The append in step2 may add a new `bound_keys` entry and prepend a cursor at a
third owner. The saved N does not grow, so the new entry is NOT visited by this
sweep. Its attachment, interner entry and dependencies are nevertheless live
for later iterations, later sweeps and subsequent replay. It is incorrect to
drop it from the next state because it lay outside this sweep's saved prefix.

**Sweep frame lemma (conditional, candidate proof).** Retain the entire ordered
raw-key prefix of length N and the representative paths used to compute each
to_i. Retain each changed entry's parent relation, post-check/discharge/scoped
payload, evidence snapshot heads/coverage, all target attachment chains,
   interner and dependency/edge/bundle state, allocation frontiers and successful
   resource outcomes. The retained evidence includes the admission record read
   by `direct_admission_head`, not merely its numeric head. Then the emitted
   ordered sweep transitions are determined; payloads
of unchanged entries need no parent-relation lookup in THIS sweep.

Proof: induction on i. Representative paths do not change inside this sweep.
An unchanged key takes the empty branch. A changed key executes the listed
constructors; retained interner/attachment/evidence state determines every
branch and identity. Include all earlier appends when processing i+1. Fixed
N proves termination of this scan, not solver termination. This frames only
this method: an unchanged entry can still be reached by another consumer, so
its parent payload cannot thereby be deleted from a complete action31 cut.

This gives a specific rejection of endpoint-disjoint framing: a physical row
not selected by one local replay may own a raw bound whose item is redirected
by a pending merge. Its global-sweep transport can prepend a fiber later used
by either family. Relation interning, recipes and generation changes remain
observable even when the final bound endpoints coincide. No fixed-source
counterexample or merge occurrence is asserted from this dependency alone.

## 5. Backward cut obligations for both families

There is also a narrower complete constructor invariant for **Effect endpoint
variants**, which does not count slots. In this fixed source, FormalEntry and
the outer `[io] int` registration retain permissions without emitting an
Allowance/Support/Contribution; the value domain is Int. FormalNameEffect emits
row/row pairs. Purity emits Bottom/row and row/Empty. Apply, initializer and
Block joins emit row/row pairs. Lambda slot4 is row/row. FreshUse, selected
extrusion copying and parent equality transport retain these endpoint variants.
Ordinary replay composes their endpoints without inventing a view; identity
context execution introduces no residual. Induction over these actual
constructors therefore confines semantic Effect endpoints through action31 to
rows, BottomPositive and EmptyNegative. The declaration of tick is not an
invocation. This proves a variant exclusion, not the full physical inventory.

At the successful return of each preceding typed drain, Transport has run
settlement at an empty worklist before proceeding to Diagnostics. Settlement
consumes its pending vector to the end. In this Effect fragment diagnostics
reports/traverses conflicts and does not add extrusion parents. Thus, at
action31's slot4 entry, the pending remainder is empty. R_L is freshly
allocated and initially has neither physical side. The initial task has R_L
only as upper endpoint. Induct over its descendant tasks: if a lower row owns
an upper bound R_L, replay produces another task with upper R_L; if R_L owns a
positive lower, its empty upper side produces no replay. Bottom/Empty checks
do not invent tasks with R_L as lower. Candidate row/row Effect processing
never calls extrusion, and this variant fragment cannot create Parent. Hence
slot4 preserves R_L's empty physical upper side, creates no equality merge,
and creates no Value Function. This is valid for each finite successful drain
prefix; no termination or resource success is inferred. It strengthens the
fresh-provider argument below without the unestablished all-Value-slot base
in §6. Its effect fibers, memos and acknowledgements still need enumeration.

One source-derived initial coordinate can be reduced further. In a successful,
well-formed constructor prefix immediately before action31 slot2, the newly
constructed F_L contains the positive live-variable term for the newly
allocated R_L. `fresh_effect_at_level` uses the prior effect-row vector length;
earlier constructor-produced live endpoints cannot name that unallocated row.
The slot4 drain in this ordinary row/Bottom/Empty fragment constructs no Value
Function. `term.rs:1126` constructs and interns the full four-child
`TermNode::PositiveFunction`; `lib.rs:14184` reads back these exact children.
Thus F_L is a new structural endpoint at this point, even if its other three
children match an old Function. The term interner is retained, not assumed to
allocate every constructor call.

Consequently, immediately BEFORE slot2, no old typed-pair key or RelationKey
contains that F_L endpoint, no physical bound item is F_L, and no saved
replay-head key has B+=(L,+,F_L). This proves absence at this specific boundary
from a fresh child, rather than guessing an empty replay tail from levels.
It does not prove absence at a later replay invocation: slot2 extrusion,
admission, duplicate physical iteration and earlier children can already have
mutated its keys. If an extrusion changes F_L, the rebuilt endpoint needs its
own freshness argument. The local generator lemma still requires its actual
heads and completion map when invoked.

Applied to the parent supplier, this removes inherited histories containing
the unconstructed provider from the pre-slot2 search. It leaves all old demand
fibers, effect/result raw memos, slot4 acknowledgements and later self-products
intact. It does not supply their concrete order or multiplicity.

The following is a source-symbol read closure, not an instantiated certified
cut. Each row is required unless its branch is proved absent from the authentic
prefix. No unknown coordinate is set to empty.

| Observation | Retained predecessor data and owning symbols |
| --- | --- |
| Provider admission | `admit_lambda_fact`: parameter position, formal domain/registration and role, actual component endpoints, current parameter level, fresh R_L row, term/store provenance and slot4 full drain before slot2. |
| Physical selected slot | `candidate_apply_value`, `candidate_insert_bound_with_evidence`, `candidate_physical_slot_bound`, `candidate_opposite_count/bound`: raw/canonical owner/item, representatives, levels, both row/atom vectors with multiplicity/order and exact lane/index, emission/admission readback and cause. |
| Replay products | §3's two different B- fibers, full cursor links and saved-head pairs, dependency membership, source sets, scopes/contexts, recipe state and interner frontiers. |
| Suppression/recapture | `pair_is_current`, `dispatch_live_item`, `mark_candidate_pair`: raw memo membership, retained extrusion rewrite, actual processing RelationId, canonical pair, completed generation. For a rewrite retain `by_output[(original TypedPairKey, reused output)]`, ordered groups/parent ranges, original sources, reuse_keys, activations, pending parents/cursor, next_occurrence and qualifying source events. |
| Equality consequences | `settle_candidate_intrusion`, `merge_candidate_rows`, §4: complete pending sequence, copy/parent forests, physical both-side append inputs, metadata/incidence, full saved sweep prefix and every resulting attachment; generation only after sweep. |
| Source qualification | `candidate_value_graph::References::qualifies`, `extrusion_sources`, `source_events`: original Value SCC components/events and actual processing relation's source-set ID. Equal endpoints or levels do not qualify an occurrence. |
| Child scheduling | `step_typed_drain`, `candidate_step_function_dispatch`: complete worklist order, task/relation/ack fields, stage/current item, processing pair and relation, Function dispatch cursor/pending item, descendants enqueued at front or back, context-consumed flag. |
| Dependency side effects | `State::dependency`, `edge`, `bundle_edge`: dependency membership, exact edge adjacency/order and logs, optional bundle-transport index, bundle incidence chains and source-bundle records. `context.lifecycle_generation` advances for a new FunctionPort dependency independently of intrusion.generation; retain its checked counter and source-support invalidation/undo state. |
| Evidence side effects | `BoundEvidence::{admit,emit,snapshot,transform,recipe}`: group keys/heads/coverage, addressed admission/emission records, snapshot and transform keys/counters, transform_children, reverse incidence and undo logs. Recipe insertion may happen without a replay child; snapshot/transform identity may change although the resulting semantic RelationId is unchanged. |
| Completion | `ReplayOperation`, `TypedDrainFrame`, `complete_replay_child`, terminal drain: operation identity/task/child vector, queued vs consumed, retired, restoration pointer, Idle/Running/Ready wait with exact ack index/drain index, replay destination, ack vector and prepared/completed cursors, diagnostics before ReturnReady. Queue transfer is not acknowledgement. |
| Allocation/interner effects | `fresh_*_at_level`, `with_term_events`, `term::BranchTermArena::{intern,positive_function}`, `relation_with_scoped`, `intern_sources`, evidence constructors, `begin_candidate_extrusion`, replay allocation: row/term/relation/source-set/evidence/operation vector lengths, queried interner keys, capacities, checked counters and resource state. Retain term-lineage brand, branch page state and the shared postfix-page allocator, not only branch node count. A no-Parent extrusion still consumes next_occurrence. |
| Return and transaction | `run_candidate_typed_drain`, terminal stages and route commit/rollback owners: prior processing restoration, diagnostics and witness lineage, journal/checkpoint state, retained child owners, publication/commit ordering. Successful source-action progression requires actual return, not only an empty worklist. |

In ordinary mode the context is IDENTITY/default scope, so filter execution
returns false before residual writes; this permits that particular branch
reduction. It does not remove full source-set identity, witness/evidence gaps,
interner events, resource checks or physical admissions. In particular an
OwnerEmission's missing processing/authentication antecedents remain gaps.
The only source-support registration constructor in this pinned owner is
`#[cfg(test)] synthetic_source_support`; an ordinary source run with no
synthetic supplier has none. Even on that empty-registration branch,
FunctionPort's checked lifecycle-generation increment remains real. It cannot
be replaced by intrusion.generation or declared zero from endpoint equality.

The cut cannot currently omit general diagnostic/transaction/resource payloads:
the terminal phase precedes acknowledgement, and checked storage accounting
and fallible reservations can reject before a selected slot is published.
This note retains them as unresolved closure inputs rather than assuming
infinite capacity or proving only endpoint behavior on an invented transition.
There is a concrete allocation reason: `term.rs:349` retains one
`Arc<TermPostfixAllocator>` across aliases of a collection lineage, and
`:1188` claims a postfix page with a checked atomic compare/exchange. Unrelated
branch page claims can affect exact subsequent Term identities and exhaustion
without changing a local row endpoint or node count. An identity-exact cut
must retain that allocator state and its claim order, or establish a separate
lineage-preserving renaming argument. Neither an absent concurrent claim nor
that renaming theorem has been established here. This is a dependency in the
already pinned owner, not a request for a new external supplier or permission
to weaken original source/formal identities.

## 6. Alternative attempted: source sort induction to exclude later sweeps

A second method investigated whether actions26–31 themselves create no Parent.
The proposed constructor invariant tags Value rows as callable, formal-Int or
call-result; polar copies inherit their tag, ordinary row links and merges
preserve tags, and Function comparison sends Argument to formal-Int and Result
to call-result. Effects in this specimen have row/Bottom/Empty endpoints and
identity contexts. Source actions26,28–30 and Lambda slot4 introduce only these
row/atom pairs. Action27 introduces a demand at level2; action31's provider
fields are at level<=2. If all physical slots and retained rewrites at the
action25 return satisfy this invariant, subsequent Int extrusion creates no
Parent, row/row processing creates no Parent, and these Function insertions
need no younger child copy. With no existing pending remainder, settlement
then takes its early-return branch and generation stays4 through action31.

The transition cases make this a plausible method, but the required base has
NOT been established for every same-class physical slot and memo rewrite at
action25. The reviewed capture inventory is narrower than that base: shared
rows are deliberately not adjacency-expanded, and its action27 Result fragment
does not certify every Effect product. Consequently this note does NOT assert
generation4 through31, no recapture, no global sweep, or omission of group/
parent contents. This is an unresolved induction base, not a certified frame
condition or a renamed solution to the original cut obligation.

The two methods therefore expose distinct discriminating inputs: the sweep
method needs the exact ordered global saved prefixes whenever an actual merge
occurs; the exclusion method needs a constructor proof of the complete tagged
base plus pending exhaustion. Neither can infer its input from the other.

## 7. Remaining premise, owner and falsifier

`R140-ACTION31-SOURCE-CUT-1` remains OPEN, owned by Luna's native source/proof
lane. Its first missing evidence is a constructor-derived action25-return
state sufficient to replay actions26–31 and slot4 without guessing physical
multiplicity, bound fibers, raw memo rewrites, relation completions, operation
frontiers or resource outcomes. Required owners are `candidate_scheme` Local
return/commit, `candidate_extrusion` physical admission/replay,
`candidate_context` relation/evidence/sweep/acknowledgement, and `lib.rs`
dispatch/terminal orchestration. The output must instantiate §5 for BOTH
demand families at their actual pop order and prove the union frame.

Next in-scope mathematical step: derive that source state, or establish the
complete tagged action25 base and use it to remove the recapture/sweep branch;
then evaluate the two saved-head product formulas and preserve every actual
acknowledgement. No execution is required by the local lemmas. This assignment
does not grant another budget or write lease after its frozen handoff.

Mutual TODO `R140-SOURCE-STATE-1`: Luna supplies/reviews the above complete
prefix certificate, with exact source constructors and frozen dependencies.
Falsifier: an additional authentic same-class physical slot, retained rewrite,
fiber/old head, stale completion, pending parent or child/ack event changes
either family's next selected transition or slot while the proposed cut is
unchanged. A candidate trace must establish its actual source emission; an
assumed-state simulation alone does not satisfy this falsifier.

Mutual TODO `R140-SWEEP-FRAME-1`: for each actual successful nontrivial merge,
record N, all ordered original keys and their canonicalization outcomes,
changed-entry parent/evidence inputs and ordered appended transports before
generation advance. Falsifier: a purportedly omitted original prefix entry
changes attachment/currentness/child generation, or an appended entry is
incorrectly visited in the same saved-N sweep.

If code evidence becomes necessary, the minimal proposal is a **provisional,
not authorized implementation TODO** to retain a read-only snapshot at the
successful action25 return and before/after action31 slot4/slot2: ordered
physical slots, bound_keys/fiber heads, relation keys/completed generation,
raw memo rewrites, pending/groups, interner frontiers and operation/ack state.
Luna must grant exact implementation/output paths and a new budget before any
observer is written or run. Falsifier is the transition divergence above;
cleanup belongs to that future implementation owner. No production change is
derived here; `NO_SAFE_CODE_SLICE` continues.

No A/B/C conclusion follows. Boundary1 Local capture/restoration, later
production `Work::Bound`, its independently licensed consumer, dynamic
receiving/read/Force correspondence and foreign continuations remain separate.

## 8. Frozen dependencies, checks and resources

Direct frozen proof inputs are the R140 contract and its explicit pins, plus
the complete 39-path manifest inherited from R138. Manifest-file SHA-256:
`8bfe31e038f1c7684ac2d9dba95164f13448e150ccb08a874bea22610fc6e04f`.
R138 proof SHA-256:
`b9b91d5250b3f05def89891cca314ad24fcf84ec711b8c6e76c7c4dcf936c467`.
R138 handoff SHA-256:
`d7504666ab99ed3822fd91c103c056e4fbb9aad344ab10f2477567ba5a8b991c`.
Parent SHA-256:
`d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`.

| Current inspected source owner | SHA-256 |
| --- | --- |
| `candidate_intrusion.rs` | `8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4` |
| `candidate_context.rs` | `002b9d86e26cfda6fdf094ea4d161501849a7127d55c2d147d408a781b9fd28d` |
| `candidate_scheme.rs` | `2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850` |
| `candidate_effect.rs` | `6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0` |
| `candidate_extrusion.rs` | `fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d` |
| `candidate_source.rs` | `cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7` |
| `candidate_value_graph.rs` | `19da9779e3e7866f5891e019e1cd343136ae0115bd1c47a02a7e7ee0cdfa80e0` |
| `term.rs` | `f3a0c3875ba1ba8c80ee48a405faf3dad22b57cba8930394f99181201bc58f60` |
| `lib.rs` | `c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985` |
| `shadow_apply.rs` | `838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543` |

Checks: static source/rule/proof reads, symbolic loop/branch arguments, live
SHA-256 comparisons; no compiler/solver execution, probe, instrumentation,
tests, builds, Git, network or delegation. Baseline validation is attributed to
Luna, not re-created by this leaf. The local conditional lemmas require fresh
independent review; this author cannot certify them.

Stage progress: source/pin intake complete; replay-generator and saved-prefix
sweep derivations, Effect-variant/slot4-sink and fresh-provider reductions
complete as candidates; whole-action31 union frame and
source-instantiated cut incomplete; parent application explicit in §§1,7.
The finite proof grant is 780 active seconds, zero Astra. Exact CPU/RSS and
provider-side active duration are UNKNOWN. The assignment handoff records a
conservative elapsed-time charge. Only this file and the assigned inbox file
were created; no scratch paths. The writer freezes both and stops after the
handoff; no descendant leases exist.

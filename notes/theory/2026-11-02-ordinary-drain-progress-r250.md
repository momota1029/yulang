# R250: ordinary typed-drain progress and the first unfunded birth

Revision 1. **Candidate static source-native derivation and precise proof obstruction; independent review pending.**
Author `/root/sol_r250_drain_progress`; no coauthors or descendants.
Contract `tasks/agent-loop/sprints/ordinary-drain-progress-r250.md`, admitted
SHA-256 `9772cca143817a6d2a5a803334f5b5047b9846154a57b3cd95be67cb5c837c7a`.
Initial contract SHA-256 was
`3f56410931a60b731345eedf0b6f77f504764004b64a6913ec1b84254913d286`;
Luna admitted only the additional read-only scope owner described below.
Baseline `f8124eba4827e89c596016bdc28019011cd1887d` matched by reading
`.git/HEAD` and `refs/heads/yulang3`, without a Git command.

## 1. Parent, domain, result and limits

The unchanged parent is Yulang inference soundness and its Rust implementation,
with the original accepted source domain, Simple-sub A/B, arbitrary independent
satisfying assignment, shared witnesses, F1/FK1 and foreign continuations.
Immediate edge: `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1` / `R70-DRAIN-1`.
No fully quantified whole-inference Lean theorem is supplied by these parent
artifacts; this packet invents none. Lean declaration, checked theorem type and
axiom dependencies: NOT APPLICABLE; checker NOT RUN, as explicitly prohibited.

Use the successful forward, non-test initialized-session domain of frozen
R249 §1, including finite successful prefixes which produce type diagnostics.
Do not assume that the suffix eventually returns. Failed-route continuation,
test-only retained resume and manually installed states supply no evidence.
R249 supplies handle lifetime/identity retention, not progress or authenticity.
All structural/evidence entry conditions not established there retain their
own original obligations; in particular, a valid diagnostic graph is not
inferred merely from a live replay owner.

**Result:** the actual dependency graph and local finite phases below are
derived; a global well-founded measure is **NOT ESTABLISHED**. The first
unfunded transition of the attempted global measures is the fresh-copy birth
equation in §4. This is a proof obstruction, not a source-qualified divergent
execution or a proof that no measure exists. No accepted infinite cycle, lost
acknowledgement, or concrete production defect was demonstrated.

The informal result types are deliberately smaller than the parent:

```text
SETTLE250:
At one actual empty-queue settlement entry with valid finite inventories,
the pass processes its finite pending suffix; each genuine merge decreases
the number of representatives by one, increments equality generation once,
and may add finite bound/fiber/replay/diagnostic work. It returns to the drain;
it does not establish that the later queue empties again.

SUFFIX250:
At actual Diagnostics entry, given valid finite diagnostic references and
the ordered authoritative ack inventory, with successful fallible helpers,
the phase creates no typed work or pending merges. Its finite graph/bucket
work finishes; terminal ranking then reaches ReturnReady and removes F.
This proves a suffix implication, not eventual entry into Diagnostics.

SCOPE250(I,S):
Over fixed finite input IDs I and scope IDs S, actual canonical transformer
composition introduces no new IDs and has at most
2^(|I| + |S|*(|I|+1)) distinct transformer values.
This bounds the transformer component only, not full RelationKey identity.
```

These are candidate source derivations, not kernel-checked declarations or
independent certification. Their application and remaining premises are §7.
Full semantic parent delta and Simple-sub A/B delta remain **zero**.

## 2. Production route and producer/consumer graph

The route is actual production code, not the test fallback or a hand-built
state: `admit_all_collected_facts` / `admit_collected_fact`
(lib:11511–11591) admits a stored occurrence and its provenance, translates its
same-kind endpoints and calls `constrain_live_value/effect`. The Lambda owner
also constructs an admitted Function-to-root occurrence and calls
`constrain_live_item_with_inferred_entry` (lib:11763–11821).
With a candidate graph, that entry immediately selects
`run_candidate_typed_drain` (lib:14096–14109); the older fallback loop cannot
simultaneously consume this queue. The function starts the frame then repeatedly
calls `step_typed_drain` (lib:14340–14366). This establishes the non-test route
to the owners below; it does not independently certify collection of every
source form or exhibit a source program producing arbitrary many births.

| Transition / exact owner | Produced or retained work and its consumer |
| --- | --- |
| `start_typed_drain`, lib:14291–14337 | Empty queue required; pushes F, clears diagnostic scratch, seeds actual relation, enqueues initial item, then publishes passive source receipt. |
| Transport with no current, lib:14411–14446 | On empty queue runs settlement first. Pop transfers one queue item to F; its exact replay ack joins F's suffix. If still empty and clean, selects Diagnostics. |
| Transport with current, lib:14447–14454; context:4186–4204 | Canonicalizes actual relation endpoints, possibly interning a Derived child. Keeps the ack's original operation/index. Selects Context. |
| Context, lib:14455–14460; context:4208–4312 | Executes retained relation before pair memoization. A first filter discharge can install/replay actual Allowance bounds; subsequent discharge is keyed by exact relation. Selects Dispatch. |
| Dispatch, lib:14461–14474,14538–14975 | Removes ack from the dispatch-local item. Duplicate memo is exact processing RelationId at current equality generation, not just endpoint pair. Canonical aliases/rewrite enqueue children; structural cases produce finite Function/Tuple/Record/Variant child arrays. |
| Structural admission/enqueue, lib:14475–14508,15059–15161 | Each child has separate admit then enqueue steps; only successful enqueue advances its fixed array cursor. Every generated child here has `replay_ack=None`. Finite array progress does not bound descendants. |
| Ordinary bound application, extrusion:1115–1175 | Inserts the physical bound/evidence, then replays its snapshot of opposite slots. Effect Support/member/tail expansion additionally enqueues finite children (effect:1606–1673). |
| Extrusion, lib:14814–14866; extrusion:22–595 | The two ordinary nonrow-to-row branches copy high rows, reconstruct finite structure/views, retain Parents and rewritten pair, and enqueue rewritten work. Final initialized Allowance replay transfers children to the same outer queue. |
| Replay, extrusion:1070–1112; context:4411–4497,4598–4619 | Snapshots actual fiber heads and prior frontier; new-lower × all-upper plus old-lower × new-upper. Child identity includes full relation/context/source/scoped payload. Exact dependency/head checks suppress already covered ordinary products; new fibers reopen products. Creates retained child vector and transfers each next index. |
| Settlement, intrusion:568–710 | Consumes pending Parent suffix; real merges append both bound sides, transport fibers, redirect representative, canonicalize bounds, advance generation, reopen diagnostic root, and replay merged owner's lowers. Adds queue work before drain can select Diagnostics. |
| Diagnostics, lib:14509–14522 | Conflict graph walk, diagnostic SCC/bucket completion, root witness replay and clear; then Acknowledgements. Detailed accounting is §5. |
| Acknowledgements / ReturnReady, lib:14986–15052; context:2536–2604 | Sequential exact child completion advances F's ack cursor; ReturnReady retains Running→Ready barrier, records passive completion and pops F. §6 supplies ranking, using R249 lifetime retention. |

`enqueue_item` reserves evidence/queue/undo before replay transfer and then
pushes infallibly (lib:15328–15355). No dispatch child carries its parent's
consuming ack. The replay child vector, transferred queue entry, current frame
and completed prefix remain distinct. R249's passive receipt exception remains
intact: completed receipts need not still name a live operation map entry.

## 3. What finite settlement and finite support actually provide

Let `P` be pending.len and `p` its cursor at one settlement call. Compression
only redirects finite existing forest paths. The loop reads `pending[p]`, calls
merge and advances p. Within that pass, merge/insert/transport/canonicalization/
replay enqueue work but do not dispatch it or call `retain_extrusion_parent`;
therefore P is fixed and `P-p` decreases. Each bound/fiber traversal uses a
finite captured prefix/head. New queue work is counted, not ignored.

For a genuine merge, `rep(copy) != rep(parent)` is checked first. The forest
edge then removes exactly one representative; equality generation increments
once (intrusion:608–618,665–697). Same-representative entries consume a pending
slot without advancing generation. Compression is not a merge. Root reopening
(lib:13585–13591) marks diagnostic completion Pending and admits its key once
into the current delta; it does not itself enqueue a typed task. Replayed
bounds do enqueue. Settlement sets dirty=false on exit; the caller pops any
resulting queue item rather than proceeding directly to Diagnostics.

If B births were independently bounded over an entire drain with R0 initial
representatives, genuine merges would be bounded by `R0+B-1` when R0+B>0.
Thus equality generations/root reopenings have a finite charge **after** a
birth budget is justified. Current representative count alone is not such a
budget, because births replenish it. Lifecycle generation advanced by new
FunctionPort dependencies (context:3583–3632) is separate from intrusion's
equality generation and does not independently pay for new relations.

The newly admitted scope owner gives a real finite component. `then`
(scope:134–176) unions stamped tags, merges scope entries, filters second
predicate tags against first stamps, and canonicalizes their union. It creates
no ID. Over I,S a stamped set has at most 2^|I| possibilities; each scope has
at most 2*2^|I| (keep flag, missing-tag subset) possibilities, including its
omitted identity case. Their product gives SCOPE250. `intern_scope`
(context:2949–2968) interns actual value equality; `compose_scopes`
(:2970–2978) calls precisely this `then`. Apply SCOPE250 to the transformer
component of replay's `ScopedFlow` at context:4465–4468. Repeated compositions
over the same support cannot create unboundedly many transformer values.

This uses no SCOPED_RECORD_LIMIT exhaustion. It does not equate different
residuals/providers/witnesses, bound demand-root rewrites, establish a fixed
support across fresh remapping, or bound endpoint/context/source identity.
In particular ContextExpr has its own structural interning (context:2784–2810),
while relation keys include context, source set and scoped flow (:3481–3513).
Replay may form `Replay(cL,cU)` unless both are identity (:4458–4461);
Function ports may form Swap/Prefix (:3935–3963). No quotient of those contexts
is invented. Conversely, their syntactic growth alone is no counterexample:
zero-word discharge (:4109–4173) can remove filters/reset replay residual to
identity before subsequent bound propagation. A productive infinity would need
an actual accepted route surviving those checks.

## 4. First exact global obstruction: births have no derived finite charge

Attempt 1 was lexicographic saturation over a finite endpoint/relation universe:
remaining genuine-merge credits, remaining (relation,generation) admissions,
then finite queue/dispatch/phase work. `pair_is_current` (lib:13594–13606) and
`mark_candidate_pair` (intrusion:423–455) support only the exact
relation-at-equality-generation completion component. New endpoint/relation
keys and later generations replenish its domain. Taking the *eventual* universe
as finite here would assume the missing conclusion.

Attempt 2 used the multiset of row levels, allowing a high-level credit to be
replaced by finitely many lower-level credits. The actual constructor has this
equation at extrusion:96–134, corroborated by fresh rows at lib:10521–10578:

```text
entry: old row r has level h > target L; r is not in this call's row map
birth: allocate fresh c at L, retain Parent(c,r,p,L,occurrence)
       insert call-local map[(r,p,L)] = c
       install opposite-polarity source link on r

rows' = rows ++ [c]       level'(c)=L       level'(r)=h
representatives' = representatives + 1
Parents' = Parents ++ [Parent(c,r,...)]
pending' = pending ++ [that Parent index] iff actual sources qualify
```

The operation-local maps are newly empty on **every** `candidate_extrude`
invocation (extrusion:34–43). They yield at most two sign-qualified copies per
entry high row *within that invocation*, as R70 §4 proves. They do not record a
globally consumed `(r,p,L)` credit. The old high row remains: this transition
adds a lower element to the multiset without removing its higher element, so
the proposed replacement ordering does not decrease. Strict level descent
bounds lineage depth; without bounded branching it does not bound all births.

The consumer does retain a successful extrusion rewrite, but its key is the
**whole original Value pair**, including the receiving endpoint
(lib:14578–14600,14842–14866,15380–15398). That is evidence against repeatedly
copying the identical retained pair. It is not a derived finite count of
distinct pairs/receivers when freshly copied endpoints may join later bounds
and replay products. Bounds physically append even when equal keys/fibers
are interned (extrusion:702–755); `attach` deduplicates `(BoundKey,RelationId)`,
not the cross-invocation source-row/target copy request (context:3702–3714).

A later qualifying merge can pay back one representative, but eligibility is
source-dependent (intrusion:306–343) and settlement is invoked only once the
queue empties (lib:14412–14415). Unqualified Parents are retained without a
pending merge. Even in a qualified case, treating birth plus later settlement
as one atomic decreasing transition would assume that the intervening queue
eventually empties, precisely the unresolved parent edge.

This is the first missing charge, before claiming a finite full relation/fiber
universe. Exact non-test route is §2 → actual extrusion branches → this deep
row arm → retained Parent/link → rewritten child/final replay → same typed
drain; settlement and memo consumers are as above. The arm is production code
accepted by successful checked helpers, not a cfg(test) constructor. **No
source program producing an unbounded family of these events is claimed.**
The body equation defeats these two candidate rankings; it does not refute
termination or rule out a stronger source-indexed sharing/credit theorem.

Mutual TODO `R250-BIRTH-CHARGE-1`, owner Luna: derive a finite, source-indexed
charge for births across the accepted ordinary drain, or give a source-qualified
counterexample. Required symbols: lib::dispatch_live_item /
retain_candidate_value_rewrite, extrusion::candidate_extrude, intrusion::
retain_extrusion_parent / merge_candidate_rows, context::candidate_context_begin_replay.
Required proof must account for fresh receivers, both polarities, visit-time
bound mutation, qualified/unqualified histories and generation invalidation.
Falsifier for a proposed credit: an actual accepted path repeats the credit
without consuming a decreasing source resource, including after a fresh receiver
or representative change. A synthetic cyclic row graph or limit exhaustion is
insufficient. No production repair follows from the absence of this proof.

## 5. Diagnostics-created work is finite at this phase, with validity separate

At Diagnostics entry semantic dispatch is no longer called. The following
closed call graph adds no typed queue entry, row, Parent, bound/fiber, relation,
dependency or pending merge; diagnostic candidates/errors are still counted.

`candidate_replay_effect_conflicts` (effect:1145–1205) traverses context's fixed
finite child graph. Pair keys are visited once; duplicate pending keys are
popped without expansion. `children` (context:3671–3678) follows existing
pair/relation/edge lists. If V,E are the reachable finite pair/edge sets, charge
one expansion per V and one scheduled edge per E, including duplicates. The
graph does not grow during this walk. Reporting only deduplicates and appends
`(occurrence,kind)` / SolverError (lib:16637–16683).

`complete_diagnostic_delta` (lib:15628–15991) fixes pair_count and computes
finite delta edge_count. Iterative Kosaraju uses visited flags and edge-position
cursors, so each finite DFS edge is scanned finitely. The SCC condensation is
acyclic; every external reverse edge discharges one pending-child count. Each
SCC is scheduled when its count reaches zero. For each SCC, direct seeds and
external-edge seeds are finite. Bucket processing marks a member on its first
arrival; only that event expands its internal reverse edges. Later arrivals
are discarded. Thus candidate insertions are bounded by finite seeds plus
internal edges, even though bucket pops may exceed member count. Finite bucket
count uses finite member_count/shape_count and checked arithmetic. An overflow
is an availability error, not normal completion. No improving-witness requeue
or semantic work production is hidden in this algorithm.

Reference validity remains a premise: outgoing children must have admitted
memos, old external children must be Complete, and indexes/witness extensions
must be valid. Current producers admit delta on Value memo creation/replacement
(lib:15400–15488) and reopening; `admit_diagnostic` deduplicates each delta key
(:15255–15269). This gives the intended local ownership map, not an independent
all-source proof that every replay-created diagnostic edge has its child memo.
In particular empty/missing executable fiber coverage must not be repaired by
assuming an authentic child; R71/evidence owners keep that issue.

The routine writes Complete memos, then calls `clear_diagnostic_scratch`, whose
unjournalled part clears **delta as well as completion scratch**
(lib:16039–16090). Consequently the caller's later Effect-root delta witness
loop sees an empty delta on these bytes (:14517–14519). This is the actual
control flow; this packet claims neither effect-root witness-report coverage
nor a reachable missed diagnostic. Value-root witness replay and reporting
are finite (:16273–16297). The final clear and debug empty-queue assertion add
no semantic work. Hence no diagnostic-created *typed work* remains after the
terminal point under this call graph; scratch and diagnostic coverage are
separate questions.

## 6. Terminal rank and acknowledgement boundary

After Diagnostics the ack vector cannot grow. Write m=F.replay_acks.len,
c=F.completed_acks. Terminal code checks top frame and
`c <= prepared_acks <= m`; ReturnReady additionally requires c=m
(lib:14990–15000). Preparation journals/reserves state and may fail, but never
dispatches work. R249 supplies the authoritative original child lifetime and
Running/Ready retention; successful ordered completion still must match the
actual operation's consumed frontier (context:2596–2604).

On valid ordered inventories and successful helpers, define:

```text
rank(Acknowledgements,F) = (m-c)+2
rank(ReturnReady,F)     = 1
rank(F removed)         = 0
```

An ack step completes precisely the next ack and increments c adjacent to it.
If this exhausts the suffix, stage becomes ReturnReady; if already empty it
moves directly there. Each case strictly decreases rank. ReturnReady moves
the retained destination barrier Running→Ready, records passive source
completion, pops F and restores enclosing processing (:15031–15051), decreasing
to zero. At most `(m-c)+2` terminal calls suffice. Neither resource failure nor
a failed ownership precheck is counted as a successful rank step.

For synchronous replay, context:4540–4576 subsequently delivers Ready and
changes wait to Idle without consuming the child twice; this gives a finite
delivery step once F has actually returned. It establishes nothing about an
arbitrary foreign continuation. R249 already excludes premature owner
reclamation; no duplicate/lost-ack source witness was found here.

## 7. Application, reuse, authority and next step

R70's reviewed conditional local extrusion result and its mutable snapshot/
queue-transfer distinction are reused exactly within their premises. Its old
source line numbers/hashes are historical; §2 uses current pins. R70's proof
author is `/root/r70_ordinary_extrusion_proof`, with credited complementary
author `/root/r70_extrusion_countertrace`; R70 closeout is Luna's reviewed
conditional disposition. R249 author `/root/sol_r249_prior_owner` supplies
successful-prefix storage retention. R249's pending-review wording is retained
in its frozen bytes; this assignment contract identifies the reviewed result
for present reuse. No new independent review of either is claimed here.
R143 was not read and its conditional finite-success result is not reused.

Before R250, R70-DRAIN-1 lacked a current all-phase producer/consumer progress
map. After R250, SETTLE250/SUFFIX250 apply at their **actual** settlement and
Diagnostics edges, while SCOPE250 applies at replay composition. They rule out
claiming that local ack loops or canonical scoped composition alone supplies
global progress. The outstanding eventual-Diagnostics edge is pinned first to
R250-BIRTH-CHARGE-1; a finite relation/context/fiber closure and valid diagnostic
consumer references still require their own justification. This does not
replace them by an assumption of termination or certify normal return on all
source histories. Parent remains OPEN; semantic delta **0→0**.

Rejected methods: decreasing queue length despite enqueue; local cursor as
global rank; strict copy-lineage depth as finite total branching; equality
generation count without a birth bound; all ContextExpr syntax as an accepted
infinite cycle; scope record limit/identity exhaustion as normal termination;
q=n as completion; producer/coauthor self-review; restriction to one selected
assignment or local foreign frame.

Residuals retain separate owners: R71 raw-slot/canonical-fiber coverage;
ordinary seed/antecedent/FreshUse/origin-to-fiber authenticity; all-path
diagnostic reference/report coverage; F1/FK1; foreign continuation;
source/evaluator soundness, hygiene, qualifying intrusion and generalization.
No residual/provider/witness lineages or independent quantifiers are collapsed.
`NO_SAFE_CODE_SLICE`: actual dispatch/extrusion and settlement/terminal owners
were inspected; no reachable approved-clause violation justifies a code edit.

Mutual TODO `R250-REVIEW-1`, Luna: fresh compiler_referee review of these frozen
bytes and especially the distinction between an unfunded proof charge and a
source-qualified divergence. Next useful producer packet must construct the
cross-invocation birth charge or attack it with authentic source constructors,
not rename the same conditional global measure. Scope/domain/dependency changes
return to Luna; this TODO grants no writes or further resource envelope.

## 8. Inputs, checks, resources and freeze

All initial pins matched before substantive source claims. The additional
scope owner's hash was obtained without reading its body, sent to Luna, and
read only after explicit admission and revalidation of it plus revised contract.
No unadmitted source owner was read/cited. Some batched display output was
truncated; relevant source bodies were reread in bounded chunks. Skills read:
yulang-proof-portfolio, yulang-sprint and the required yulang-lean-proofs policy;
no Lean work was performed under the explicit source-only prohibition.

Checks: read-only ref observation, SHA-256, source/symbol searches, static
constructor/consumer and ranking arguments, output whitespace/hash checks.
No tests/builds/probes/Cargo/Lean, production/test/expectation edits, Git command,
external contact, descendants, nested CLI, model switch, runtime/quarantined
paths, scratch/cache/generated output. Only the two exact leased files written.
Requested model/effort `gpt-6.1-sol/high`; observed model/effort UNKNOWN.
Worker `/root/sol_r250_drain_progress`, session
`01a1873a-a93b-7dc3-a8ce-028a7b543a80`; parent task/admission messages supply
the current launch/work receipt. Provider active time/CPU/RSS UNKNOWN. Maximum
2400 active seconds, no reset, expansion or carryforward. First explicit clock
2026-11-02 04:39:10 UTC; final resource/clock receipt is in the handoff and
external freeze message, with conservative charge including setup.

All dependency SHA-256 pairs, final revalidation required at freeze:

```text
429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be  crates/yu-solver/src/lib.rs
a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905  crates/yu-solver/src/candidate_context.rs
475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97  crates/yu-solver/src/candidate_intrusion.rs
6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e  crates/yu-solver/src/candidate_scheme.rs
bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49  crates/yu-solver/src/candidate_source.rs
80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61  crates/yu-solver/src/candidate_extrusion.rs
4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15  crates/yu-solver/src/candidate_effect.rs
d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1  crates/yu-solver/src/term.rs
4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03  crates/yu-solver/src/candidate_scope.rs
648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7  notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md
4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf  tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md
25f6a370ae1aa2d7a623a8aa0eaede979248d85b8c03c894fbf8f7850775e8db  tasks/agent-loop/inbox/20261019-r70-proof.md
ff2c149bd71c783f874c150404bf199084858df631c21899d3abf53a258655bb  tasks/agent-loop/inbox/20261019-r70-closeout.md
a93b2e5d38c03511c768dd704e57f3b616a1dafc591fe62a4155d64a06bbf4d8  notes/progress/2026-10-19-r70-closeout.md
615121840e60fe86b493a3e9b9236783770cc8bbd002cea6c4e41b29d60e90e9  notes/theory/2026-11-02-prior-replay-owner-lifetime-r249.md
381d7d65f8de903611e9896fc56498a4ce005b551c08d073b63e9c891657a246  tasks/agent-loop/inbox/prior-replay-owner-lifetime-r249.md
```

All new paths: this note and
`tasks/agent-loop/inbox/ordinary-drain-progress-r250.md`. Scratch NONE;
descendants/unresolved descendant leases NONE. Theory hash is recorded in the
handoff; handoff hash is returned externally to avoid recursive self-hashing.
Writer state after final checks: **STOPPED / WRITES_STOPPED**. Revision 1 freezes
both outputs for Luna intake; review/adjudication/integration remain pending.

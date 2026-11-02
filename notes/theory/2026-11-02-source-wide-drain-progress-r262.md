# R262: receiver renewal across a settlement cut

Revision 1. **Candidate source derivation with a localized progress obstruction;
independent review pending.** Sole author
`/root/sol_r262_source_wide_drain_progress`; no descendants or coauthors.
Contract `tasks/agent-loop/sprints/source-wide-drain-progress-r262.md`, SHA-256
`3cae007dd0fb6ed247ca16784ec8f7a8196718bf4c671cf23ddaa9ca73372355`.
Fixed pre-assignment baseline `8a0ddd2ee35b7e5f9ab3dd2fe473457000c42660`.

## 1. Original claim and exact outcome class

The unchanged parent is Yulang inference soundness and its Rust implementation
for the original accepted source domain and Simple-sub A/B quantifiers,
including arbitrary independent satisfying assignments, shared witnesses,
F1/FK1 and foreign continuations. This packet concerns only
`R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1 / R70-DRAIN-1`, through
`R250-BIRTH-CHARGE-1 / R253-LATER-TRIGGER-1`. The current source argument uses
the inherited initialized, non-test, successful-forward session domain, with
successful helpers and actual finite prefixes; it does not assume eventual
Diagnostics entry. R70's local `W` premise remains separate. No Lean theorem,
checker run, or axiom-free claim is made.

**Result:** `SETTLED262` below proves a source-local exhaustion property after
one actually processed qualified Parent. It excludes a repeated birth from
the same canonical raw parent and target *after that settlement*. It does not
bound the earlier queue epoch, unqualified retained groups, or distinct raw
parents with the same entry projection. A source-wide productive-renewal rank,
uniform multiplicity, eventual Diagnostics entry, and the full parent remain
OPEN. No accepted-prefix rank-preserving recurrence or divergence is certified.
This is a candidate partial source result awaiting fresh independent review,
with parent/A/B delta **0 → 0**.

The initial exact byte gate matched the R255 manifest SHA-256
`f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`
and **36/36** direct pins before source-body reads. The R262 admission record
is SHA-256 `29fdb4466853d7ec4b7ddff97e5bbfdef3b19ffceee15e65b763829720da44b6`.
Contract-listed R250–R261 dependencies retain their exact contract hashes;
R261's changed inbox is quarantined and was not read. Actual runtime model
instruction reports `gpt-6-sol`; requested Sol/high; observed effort and
session UUID are UNKNOWN. No worker Git, source edit, build, test, Lean, probe,
scratch or generated file was used.

## 2. Source-grounded renewal control

Use a finite *control skeleton* plus unbounded identity registers. The skeleton
contains the entry structural template/subtemplate (R252), selector name and
sign (Function's four ports, ordered Tuple/Record/Variant selectors, recognized
Effect view), source event subset/qualification flag, birth target in the finite
entry level alphabet (R251), and transition kind below. The registers retain
raw Value/Effect row and Term IDs, canonical representatives and current levels,
physical owner/lane/slot and exact raw/canonical BoundKeys, RelationIds and
Context/scoped/source payloads, replay heads/prior heads and Dependency keys,
the whole original pair and its retained rewrite, occurrence/group/Parent
indices, pending status and equality generation. Projecting away those
registers gives finite control but is **not** a finite reachable-state proof.
R252's entry-finite parent words likewise have unbounded raw fibers.

The only birth transition in this drain SCC is a deep `Work::Visit` inside
`candidate_extrude`: for canonical parent row `r` with current level `h>L`,
it creates a fresh same-kind `c` at `L`, retains
`Parent(c,r,p,L,source,comparison,occurrence)`, inserts the opposite-polarity
source link on `r`, and records the call-local `(r,p,L)→c` map
(extrusion:24–43,96–185; intrusion:305–366). The old high row remains. Its
Parent is pending at birth exactly when the actual processing source set
contains an event satisfying `references.qualifies`. Reuse of the exact
original full pair invokes its retained rewrite and can activate an old group
once; it does not rerun this birth (lib:14565–14615,14814–14866,15380–15398;
intrusion:368–420; reviewed R251).

The renewal transitions that can expose a copied row as a new receiver are:

| Kind | Actual producer and guard | Required consumer before another birth |
|---|---|---|
| Structural selector | A successful Function/Tuple/Record/Variant comparison admits ordered port children, retaining actual relation/context/sources; source shapes may include Record/Unit formals (lib:14900–14970,15059–15161). | Child reaches the canonical row/nonrow dispatch, passes memo/current/rewrite and has a deep structural Visit at its then-current receiver level. A selector step descends a template, but another replay can later return to its root. |
| Ordinary bound replay | `candidate_apply_value/effect` inserts one addressed physical bound and calls `candidate_replay_bound` against the current opposite prefix (extrusion:1070–1185). | Context's new/old fiber quadrants and exact `Dependency::Replay` novelty emit the raw task; Transport/Context/Dispatch then pass (context:4411–4497; lib:14411–14485). Source-link insertion itself does not call replay. |
| Settlement replay | Only after the typed queue is empty, pending Parents merge; copy bound sides/fibers are transported, the representative and level change, and canonical bound keys are transported before replaying all merged lowers (lib:14411–14446; intrusion:560–710; context:4649–4678). | The emitted child must survive the same exact relation, memo, canonical representative, rewrite and source guards. Merge replay may create a *later* trigger, including the reviewed finite R259 route. |

For an ordinary replay, `begin_replay` compares exact current and recorded
heads, combines each new lower fiber with all current uppers and each old lower
with new uppers, and admits a dependency keyed by child RelationId, both input
RelationIds and both exact BoundKeys. Duplicate dependencies are suppressed;
`drive_replay` transfers children to the outer queue without dispatching them
(context:4411–4497,4625–4647). Thus the link born by a child's own extrusion
cannot be consumed by that same replay call (reviewed WAVE253). Each supposed
productive control transition must retain its actual emitted child and
successful dispatch; matching endpoint shapes or an origin table is not
enough. REF261/FIB261 supplies only bounded child reference facts at reached
Diagnostics cuts, not this renewal rank.

## 3. `SETTLED262`: exhausted parent-target birth after actual settlement

Fix a raw row `r` of either kind, an actual birth at target `L` from the then
canonical representative of `r`, and its actual Parent index `j` for copy `c`.
Suppose `j` is in the pending suffix, either qualified at birth or activated by
recapture, and a successful `settle_candidate_intrusion` processes `j` to
completion. Then, from that cut onward in successful forward execution,

```text
current_level(rep(r)) <= L.
```

Consequently any later `candidate_extrude` Visit that canonicalizes this same
raw `r` and targets `L` stops at the row-anchor branch and allocates no fresh
copy of that class at `L`. This conclusion is about the actual canonical row
and target, not all rows with the same R252 parent word or all lower targets.

Proof by the two source branches. Immediately before `merge_candidate_rows`,
if `rep(c) != rep(r)`, the merge copies both bound sides, then makes the
surviving parent class level `min(level(rep(c)),level(rep(r)))`; the copy was
born at `L` and levels only lower, so the result is at most `L`
(intrusion:599–690). If the representatives already coincide, that same class
contains `c`, and the minimum-level invariant of reviewed SETTLE254/MIN254
already gives level at most `L`. Later genuine merges take another minimum;
no successful forward constructor raises a class level. Each Visit begins
with `canonical_extrusion` and tests `original_level <= target` before the
fresh-row arm (extrusion:71–111). The retained original structural Term may
still contain a raw handle for `r`, but that Visit canonicalizes the row
before this test; no raw-handle exception restores `h>L`.

The `qualifies` test is used only to establish that `j` was actually pending
and processed. It is computed from the source event SCC association
(`candidate_value_graph:332–405`) and the exact processing relation's source
set (`intrusion:319–343; context:3523–3538`), not from a row level or a
syntactic self-reference. An unqualified group may be activated later by
recapture only under a new actual source set. Until that activation and actual
settlement, this lemma says nothing about further births. Nor does a merely
pending Parent lower `r`: settlement waits for queue emptiness.

This result is compatible with R259. Its reviewed 27-Parent settlement lowers
the classes of those Parents; its later ten Parents come from the two distinct
whole receiving pairs `(H_h,U_z)` and `(H_l,U_z)` and their then-high structural
parents. `SETTLED262` does not charge them to an already exhausted identical
canonical `r,L`. R259's source-derived two-pair debt, complete carrier and
second settlement supply a finite certificate for that one accepted route;
they are not a source-wide multiplicity bound.

The source-set transition also gives a limited ancestry fact, `QUAL262`.
For an actual direct Context derivation from relation `rho`, the child retains
`rho`'s source-event set; for an actual Replay derivation from input relations
`rho_l,rho_u`, its child has their union. In the frozen drain, source actions
do not interleave, so these are the only ways a descendant relation obtains
its event set (context:3449–3453,3527–3538,3812,3919–4079,
4186–4208,4317–4358,4411–4478,4649–4673,4706–4775).
Writing `Q(rho)` for “its source set contains a source event whose sealed
origin/receiver SCCs coincide,” every direct derivation satisfies
`Q(child) >= Q(parent)`, and every Replay satisfies
`Q(child) = Q(rho_l) or Q(rho_u)`. The actual `qualifies` test is
`candidate_value_graph:355–405`; a fresh source seed is an entry input, not
an arbitrary event injected during this drain. Thus an unqualified Replay
child has two unqualified input relations, and an unqualified direct child
has an unqualified parent. This is a relation-lineage property, **not** a
claim that all worklist tasks carry a relation or that SCC membership is a
decreasing source rank. A qualified descendant can reach an old unqualified
group's rewritten output and activate it through the actual recapture guard;
until it does and that Parent settles, `SETTLED262` cannot be applied.

## 4. Size-change attempts and the first unproved equation

The finite-control transition analysis has three genuinely different edges:
raw Parent ancestry strictly lowers its birth label (R251); a structural
selector descends a finite entry template (R252); replay can return to a
template root with a same-level receiver (R252/R253). `SETTLED262` prevents
reusing the same canonical parent at the same `L` *after* its Parent is
processed. It supplies no descent at the birth itself. The source link is
attached with no opposite replay and the parent retains its high level while
typed work remains; another distinct original pair may invoke a fresh local
map before the first settlement. This is exactly where a source-wide
size-change cycle may renew without a proven decrease.

Three candidate scalar ranks fail as deductions from the current source facts:

1. **Strict receiver-level descent.** It would require `L_next < L_now` for
   each productive renewal. In the reviewed accepted ordinary R257 route,
   `Visit(y,+,1)` creates `c_y` at level 1. A later actual `J_h` insertion on
   y replays against `(y,-,c_y)` with the exact new/new fiber dependency and
   emits `(J_h,c_y)`; its first successful dispatch deep-Visits at `c_y`'s
   *same* current level 1 (R257 §§2–3). This is a real finite source prefix,
   not an abstract control cycle or divergence. Raw Parent birth labels still
   strictly decrease on their own ancestry (R251); that fact is untouched.
2. **Pending Parent count / settled receiver debt.** Birth can increase
   pending count before a merge; merge is delayed until the worklist empties.
   The reviewed R259 route has 27 Parents in its first suffix, then ten new
   Parents in its next suffix. A rank requiring monotone decrease of this
   count across every generation would reject that finite accepted route.
3. **Source event or replay-head count.** `qualifies` is a pure SCC test;
   `union_sources` retains event membership and `attach` retains actual
   `(BoundKey,RelationId)` fibers (value_graph:355–405;
   context:3523–3538,3702–3715). A qualified event is not consumed at a
   Parent birth; one event can qualify several Parents in one structural
   extrusion group (R259's five-Parent blocks). A replay head advances only
   relative to the current finite fiber prefix. New ordinary bound admission,
   copied-fiber transport and equality canonicalization may attach later
   fibers and supply new dependency keys. No entry-uniform cap on those
   attachments follows from head advancement alone.

For a fixed row `r`, sign `p`, target `L` and episode ending at the first
processing of one of its qualified Parents, let `S_E(r,p,L)` count its distinct
fresh sibling copies. The call-local map admits at most one such copy per
birth-producing invocation, and R251's retained whole-pair rewrite admits at
most one successful birth invocation per exact original pair. Hence the exact
finite-prefix charge is

```text
S_E(r,p,L) <= #{distinct successful original full pairs in E
                 whose local work visits canonical r at sign p and target L}.
```

This is a real injection into exact pair identities, but the set on the right
is not entry bounded. Every such pair is reached from a finite entry work
root, a structural port child, or a newly admitted replay relation; within
one queue epoch the equality generation is fixed and a current relation
cannot perform its structural dispatch twice (lib:13593–13606,
14411–14446; intrusion:423–455). Finite entry templates bound the length
and branching of a *replay-free* structural-selector descent. They do not
bound how many new `Dependency::Replay` keys can reset that descent, or how
many new exact receiver/hole rows those keys can carry. In R259, this count
is independently bounded by its source-derived two-pair carrier; that
route-specific fact cannot be reused as an all-source bound.

The exact first unfunded *episode* equation is therefore:

```text
Q262-EPISODE(r,p,L):
  before the first actual settlement of a qualified Parent born from
  canonical r at target L, or for a retained group never so activated,
  bound from drain-entry data the number of distinct successful original
  full pairs that (a) reach a deep Visit of that r,p,L and (b) survive all
  raw/canonical replay-head, RelationId/Context/scoped, dependency, source
  qualification, memo/rewrite and current-representative guards.
```

For an unqualified group that never activates, a source-event SCC DAG rank
would require a *constructor-to-causal-edge* theorem: each renewed pair must
advance along an actual strict cross-component source edge. The implementation
stores and unions event sets, not such a consuming path, so `qualifies=false`
alone does not justify this rank. `QUAL262` does show that an unqualified
relation chain has only unqualified ancestors, including both inputs of
every Replay on that chain; it does not orient their source ownership. For a
qualified group, `SETTLED262` bounds
only the post-settlement tail; Q262-EPISODE must bound its siblings before the
first queue-empty cut. A finite R252 projection cannot pay this number because
raw receiver/hole identities remain in its fibers. An abstract projected cycle
does not establish a source-realizable recurrence; no such recurrence was
certified in this assignment.

The owning source-to-consumer path for this equation is source Fact/Lambda/
Apply and `candidate_value_graph::seal/qualifies` → actual relation/source
transport in Context → `dispatch_live_item`'s exact pair/rewrite guard →
`candidate_extrude` deep Visit and link/Parent → actual ordinary or merged-
lower replay's physical slot and fiber heads → Context dependency admission →
next Transport/Context/Dispatch. The first missing evidence is an entry-only
bound or a concrete accepted finite prefix that exceeds a stated candidate
episode debt while all those guards pass. A synthetic graph or an abstract
cycle is insufficient. Q262-EPISODE is a named open equation, **not** a new
assumption used to conclude progress.

## 5. Application to the unchanged parent and TODO

Before R262, R250/R251/R252 left the cross-invocation distinct-pair charge
unfunded; R253 isolated the later trigger and R259 exhibited one finite
renewing route. `SETTLED262` now excludes all future births of the identical
canonical parent and target after that Parent's actual settlement, so any
source-wide renewal argument must pay the pre-settlement episode, an
unactivated group, or a different raw parent/target. It does not provide an
entry-uniform number of episodes or their widths. R251's
`B_t <= P0*(3^C_t-1)` and the R250/R251 merge bound therefore **cannot** be
instantiated with an entry-only `C` bound. Eventual Diagnostics and R70
global drain remain OPEN; this packet does not apply SUFFIX250 to an absent
cut. Its source-local exclusion is the only candidate parent-edge reduction,
pending independent review.

Mutual TODO `R262-EPISODE-BUDGET-1`, owner Luna's next admitted source/proof
lane: prove Q262-EPISODE with actual source-plan ancestry and replay/port
causality, or give a fully source-qualified finite accepted prefix that
repeats a proposed debt while emitting a fresh full-pair birth. Required
inputs: the R255 36 pinned owners, reviewed R250–R259 limitations, the exact
R260/261 reached-cut facts, and a candidate numerical or well-founded episode
rank stated before searching for its falsifier. The decisive falsifier is an
accepted pre-settlement or never-activated recurrence with the same proposed
debt, new exact productive pair, actual input fibers/dependency, and unchanged
or nondecreasing rank. Source plan qualification cannot be inferred from a
single event label or Link as row equality.

Separate open owners: R70 entry W; relation/context/fiber closure (Context
and replay owners); full R71 authenticity/coverage; diagnostic adequacy and
successful helpers; Simple-sub A/B, principality, generalization, F1/FK1,
foreign continuations and native/source correspondence. No safe Rust code
slice was established after inspecting extrusion/context and intrusion/lib.
No production edit, semantic change, accepted-domain narrowing, or new Lean
packet is justified by this candidate.

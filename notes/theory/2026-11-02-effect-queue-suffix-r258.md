# R258: mode gate and an ordinary queue-suffix calculation

Revision 1, candidate freeze ID `R258-EFFECT-QUEUE-SUFFIX/r1`.
Author `/root/sol_r258_effect_queue_suffix`; no descendants or coauthors.
Requested `gpt-6.1-sol/high`; observed model/effort **UNKNOWN**.
This is source-level symbolic reasoning, pending Luna's independent review.
There is no executed parser/solver witness or checked Lean declaration.

## Parent, domain and result boundary

The parent remains Yulang inference soundness and its Rust implementation,
including the accepted source domain, original Simple-sub A/B quantifiers,
independent satisfying assignments, shared witnesses, F1/FK1 and foreign
continuations. The local edge is `R70-DRAIN-1 / D253 / SOURCE254-COINCIDENCE`.
Parent/A/B delta is **0 to 0**. This calculation concerns the particular
constructor route of R256/R257, not every accepted source program:

```yu
my outer x = {
  my k a b = b;
  my g p y = { y 0 0; p y; g p k; g x k };
  g
}
```

Use successful initialized realizations of these ordinary HIR constructors,
with `g`'s body a StatementBlock, the displayed unparenthesized applications,
and no extra expression/annotation wrappers. The distinction matters to the
exact Parent list. This is an analyzed subcase of the unchanged accepted
domain; Record/Unit alternatives and other HIR shapes are not removed from
the parent. All ordinary resource admissions on the finite prefix are
assumed to succeed; the result does not assert that an actual invocation was
run or that the whole source computation finishes.

There are two distinct source modes. The explicit scoped experiment rejects
this route during collection, before any typed queue. The ordinary entry
does admit the constructors and all its scoped payloads are default. The
ordinary calculation below gives a source-level proof of a small-step contraction of Effect
steps, not a numeric dump of every replay fiber/pop. Its claim is a candidate
certificate of the first pre-settlement empty queue and its 27 actual Parents,
followed by a productive row/Function consumer after settlement. The proof
of the contraction and the completeness of that inventory are part of the
review target; a finite transformer set alone is not used as a certificate.

No full source-wide exclusion, uniform multiplicity bound, divergence,
production defect, full Parent-theorem closure or semantic promotion follows.

## Receipt and frozen inputs

Active-work receipt: `2026-11-02 07:04:54 UTC`, actual current child task
`/root/sol_r258_effect_queue_suffix`. The runtime exposes no session UUID or
model/effort metadata to this worker: these observations are **UNKNOWN**.
There are no descendants. Exact write leases are this note and
`tasks/agent-loop/inbox/effect-queue-suffix-r258.md`; scratch paths: none.

Contract `tasks/agent-loop/sprints/effect-queue-suffix-r258.md`, SHA-256
`93b04391064712b637151177e2f7b5e8f9fc37e6fda17143bc5888befb03cfa5`.
Baseline `241d75f5a2bed8394790c3504dfdb3359edaf879`; Luna reports the sole
subsequent movement as administrative assignment checkpoint
`faefc3eb23423859fee9c6f3f89131f6a056a3c5`. This is primary-supplied ref/diff
evidence, not an independent Git-object audit. No Git command was run.

Before citing source bodies the worker's read-only SHA-256 gate returned
**36/36 MATCH** for the exact manifest in
`tasks/agent-loop/sprints/source-owner-coincidence-r255.md`, whose SHA-256 is
`f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`.
The R258 contract and all six frozen R257/R256 inputs also matched:

| Input | SHA-256 |
|---|---|
| R257 contract | `954aa1b30fbf00c730d14facac89a468d21945710a224394bac2050b16c84d1d` |
| R257 theory | `97d9c27dd9715d5e5dd9f9013f386bd86d1ac4f6260b503aed18566d5132ef9a` |
| R257 inbox | `30a95bea6689a0538477a67931a6845cf6a0071b872dd916f7b0f430dbf72a7c` |
| R257 reviewed history | `e125477efb8706c3e20af3f308b6fe1cb2bea7a53a82084f084c5355784c1f1e` |
| R256 theory | `64587485ffa245dde82a9b8379ca75ca2e66df33dbfe2d3f3eca7efbe4f23d25` |
| R256 reviewed history | `6db7b08ab2c1f961b6fc76d1d457046ecbda7a3299ede078e79555e03b46ced4` |

R257 author `/root/sol_r257_late_seed_replay`; R256
`/root/sol_r256_selected_lower_chronology`; R255
`/root/sol_r255_source_coincidence`; SETTLE254/MIN254
`/root/sol_r254_opposite_leaf`; STORE253/WAVE253
`/root/sol_r253_receiver_ancestry`. Repository source authorship is unchanged.
No source dependency was added. Read/applied: root/base instructions,
goal-driven sprint rule, assignment protocol, sprint/portfolio skills,
Lean skill's evidence boundary, design-authority and the Authoritative
inference top-level principles. Lean theorem types/axioms:
**NOT_APPLICABLE / NOT_RUN**, not an axiom-free theorem claim.

## 1. Resolve the source mode before manufacturing a scoped suffix

The actual entrypoints are distinct, with no internal fallback:

```text
CandidateInference::solve(hir)
  -> solve_mode(hir,false,false)                         shadow_apply:1586
CandidateInference::solve_scoped_experiment(hir)
  -> solve_mode(hir,true,false)                          :1643
both -> solve_hirs_mode_with_role_sources
  -> collect_candidate_world_scoped_v1(...,scoped,...)   :1822
  -> InferenceSession::try_new_candidate(batch)          :1832
```

The `?` on collection precedes session construction. A caller can attempt a
new ordinary invocation after a scoped error; that is a fresh mode selection,
not continuation of the failed private scoped state. The displayed ordinary
route is not silently changed into scoped execution or vice versa.

For scoped collection, the outer Apply of `(y 0) 0` sees an Apply callee and
calls `scoped_result_callee` (source:1839). That helper's stack executes:

```text
[Apply(Name(Parameter(y)),Integer(0))]
 -> [Name(Parameter(y)),Integer(0)]
 -> [Name(Parameter(y))]
 -> Err(ComponentIdentityExhausted).                    source:524-550
```

The stack's right end is the top. It accepts ModuleDef Names and primitive
literal/Operation forms, but not Parameter Names or Local Names. This is the
first such guard in the named route: k's initializer has no Apply, and this
is g's first statement. The later `(g p) k` would fail the same helper at its
Local(g), but it is not reached. Earlier resource/HIR/preflight rejection can
only reject the attempted entry sooner. Thus the scoped route has no runtime
`f_yh`, no late-delivery cut, and no runtime Parent suffix to settle. Calling
this an empty-queue success or a scoped Effect self-pair rejection is invalid.

The omitted-y construction still explains the *conditional local* formula
requested in R257. Unannotated ordinary y is a Value formal (source:1109-1114)
and an omitted formal (1288-1296); its Name retains its formal registration
(1155-1170). Apply admission obtains its original Lambda's omitted record,
original negative Function demand `U_y`, invocation row `I_y1`, source checking
and cause (shadow_apply:4346-4375). In scoped seed slot 0 the flow is

```text
d_y = (original_call=y1, use_instance=0, root=U_y,
       output_scope=scope(y 0), input=InputRouteId(call(y1))).
```

Replay retains the upper demand and requires no lower demand. At a local
Function comparison with upper root U_y, `candidate_function_port_admit`
authenticates `d_y.root` against that exact original negative Function,
consumes the demand, and admits the four children with transforms

```text
Argument 0; ArgumentEffect stamp_input(input_y);
ResultEffect protect_body(output_scope_y,input_y); Result 0.
```

This is context:3924-3988, not a hand-chosen label. In particular its
ResultEffect would be `(R_Jh,I_y1)` with `protect_body`, and the scoped
nonidentity-self guard must run before memoization. It is not source-created
for this HIR in scoped mode. No conditional construction here bypasses that
collection guard.

For ordinary entry, `start_candidate_graph` sets `scoped_enabled=false`
(scheme:2531), FreshUse produces default flow (context:4697-4712), and seed
does not enter the scoped branch (3814). The original introduction record
does not itself install a scoped demand. Consequently the actual ordinary
Function ResultEffect child **is**

```text
f_yi = FunctionPort(rho_yi,ResultEffect,Preserve),
pair(f_yi)=(R_Ji,I_y1), Context=identity, scoped=(0,None), i=h,l.
```

Both uses are independent. This follows from the real entry flag, not a mode
chosen to avoid the guard.

## 2. Exact ordinary transition blocks and the Effect invariant

Keep R257's actual `B(parent;owner,side,item)` attachment and ordered
`Replay(lower_fiber,upper_fiber)` expressions, with all source sets and
dependency input keys. An expression identifies its constructor and inputs;
it does not assert that different expressions have different interned IDs.
Use `E_Ji,R_Ji,E_Ii,R_Ii` for k_i's outer/inner entry and returned Effect
rows, distinct for h,l; `E_V,R_V` for g's inner Lambda; `E_G,R_G` for outer g.
`I_t,C_t` are invocation/application Effect rows for Apply t, where
`t=y1,y2,p,h1,h2,l1,l2`. `D` is the g body Effect row, distinct from body
Value row b_g. `N_yp` is the Effect row of the y Name used as argument of p y.

The precise small-step replay block used below is the source specialization
of extrusion:1070-1112 and context:4411-4497,4598-4647:

1. On dispatch `(L,U)` with processing fiber r, choose the actual storage
   owner/side by current levels (extrusion:1115-1176). Append/read back its
   physical slot and attach `B(r;owner,side,item)`.
2. Visit opposite physical slots in increasing vector order: direct rows,
   then atoms. For each slot take the actual lower/upper BoundKeys. Iterate
   their linked fibers newest-first, with the two exact ranges
   `new_lower x all_upper`, then `old_lower x new_upper`. Do not replay
   old/old. For each pair construct the source union and ordered Replay
   dependency; omit exactly dependencies already present.
3. Append every retained child to the queue's back, preserving those loop
   orders and its replay acknowledgement. The child is not dispatched in
   this block. Function admission instead admits Result, ResultEffect,
   ArgumentEffect, Argument and front-inserts each, giving the execution
   order Argument, ArgumentEffect, ResultEffect, Result.

These blocks retain physical/fiber multiplicity; no source-set quotient or
invented canonical fiber replaces an input. They also specify the order of
Effect children between the displayed Value events.

**ORDINARY258 invariant, before the first settlement:** representatives and
levels are unchanged; every relation has Context identity and scoped default;
every Effect pair has lower in `{EffectRow,BottomPositive}` and upper in
`{EffectRow,EmptyNegative}`; there are no annotations, Allowance/Support,
Contribution, operation, field, capture-incidence or provider endpoints here.
The original source facts and fresh k graphs satisfy this invariant. Function
ports, whole-Value rewrites, ordinary attachments, fresh transports and Replay
preserve it: identity Context is closed by Swap/Preserve/Replay, scope
composition is `0 then 0=0`, sources only union existing Apply events, and
Effect application inserts/replays exactly those endpoint forms.

This decides every Effect guard, including a self-pair: its transformer is
0, so context:3486-3488 and 4226-4229 do not reject it. Context then returns
unconsumed at 4250; equal Effect endpoints return successfully at
extrusion:1155-1157. Nonself rows use ordinary storage; the only nonrow/nonrow
case is BottomPositive/EmptyNegative, accepted at effect:1611. Effect work
neither generates Value tasks nor creates an extrusion/Parent. It cannot
change a Value representative, level or memo entry. This is why its
contraction is valid here; identity Context alone would not suffice in the
scoped experiment.

The actual relevant Effect source spines are:

| Source edge | Subsequent consumer |
|---|---|
| `I_y1 -> C_y1` (Apply slot 2) | `C_y1 -> C_y2` (second Apply slot 1), then `C_y2 -> D` (statement slot 51) |
| `I_y2 -> C_y2` (slot 2) | `C_y2 -> D` |
| `I_p -> C_p` (slot 2) | `C_p -> D` |
| `I_t -> C_t`, `t=h1,h2,l1,l2` | first-Apply C goes to second-Apply C by slot 1; second-Apply C goes to D |
| `D -> R_V` | Lambda slot 4 |
| `E_V -> R_V` | Lambda slot 3, Value-entry forcing |
| `R_V -> I_h2`, `R_V -> I_l2` | actual D_h/D_l ResultEffect ports |
| `R_G -> I_h1`, `R_G -> I_l1` | actual B_h/B_l ResultEffect ports |
| `R_Ih -> I_y2`, `R_Il -> I_y2` | each actual I_h/U_z and I_l/U_z ResultEffect port; the callee is an Apply, so it has no omitted-formal demand |
| `E_Ji -> R_Ji`, `E_Ii -> R_Ii` | isolated k_i Lambda slot 3 |

Lambda body Effect rows also have their slot-4 edge to R_Ji/R_Ii. Their only
propagated lower before the named k copy is BottomPositive, not a row Link
from the body into the returned row. At equal level 2, a row/row Link is an
upper on its lower owner. This orientation is essential below.

For example after the negative copy `r_Jh^-` exists, f_yh installs upper
`I_y1` on R_Jh and, by the replay block, sends its actual lower fiber and
f_yh's attached upper fiber to `(r_Jh^-,I_y1)`. Since 1<2 that dispatch
stores a lower on I_y1 and queues its replay through `C_y1,C_y2,D,R_V` in
that order along the path. All transforms are 0, all representatives are the
original rows, and every source is the actual union of these inputs. At R_V
it meets both independent invocation consumers I_h2 and I_l2 when their
uppers exist; each child goes to the back. The cycle through second-call C,
D,R_V remains real work. It is not erased by the Value table.

More explicitly, for either independent use i the source-link lower fiber
is `ell_Ri=ExtrusionLink(delta_i;(R_Ji,+,r_Ji^-))`. Its sources are those of
the actual J_i/c_y operation, including e_l1 and e_p. The upper fiber is
`B(f_yi;R_Ji,-,I_y1)` with sources `{e_i1,e_i2,e_y1}`. Their replay therefore
has exactly the union of these source sets and default flow. The inner k
consumer similarly has `f_zi=FunctionPort(rho_zi,ResultEffect,Preserve)` on
`(R_Ii,I_y2)`; its actual negative-copy lower replays into I_y2, then the
Apply slot-2 Link C_y2, D and R_V. This accounts for the returned Effect of
both outer and inner k Functions and both h/l uses. No Effect Link in these
paths is interpreted as endpoint equality.

## 3. Value queue projection and complete signed copies

The Effect invariant proves projection preserves Value order: deleting an
Effect pop and its Effect-only back insertions leaves the same relative
Value sequence. It does not permit moving a replay child ahead of a pending
Value task. The SourceAction drains and initial chain through A_h,A_l,
B_h,B_l,C_h are R256's reviewed chain. Starting from its first x/U_p pop,
the projected queue is:

```text
[x/U_p,C_l,D_h]
 -> [C_l,D_h,x/U_p']
 -> [D_h,x/U_p',D_l]
 -> [x/U_p',D_l,J_h/y]
 -> [D_l,J_h/y]
 -> [J_h/y,J_l/y]
 -> [J_l/y,J_h/c_y,J_h/U_y]
 -> [J_h/c_y,J_h/U_y,J_l/c_y,J_l/U_y].
```

Here D_i includes its actual four front children. Its Argument is k_i/y,
whose own replay appends J_i/y; its Result b_g/w_i adds only an upper on
b_g. The low final-expression Group already has w_l/b_g, so those last two
body rows may form a row-Link cycle. Neither has a Value lower, so this adds
no structural task. The rewritten x/U_p' inserts at level 1 unchanged.

Let `q1,q2` be the distinct literal Value rows and `Int` their positive atom.
In the following table all four front children are executed, including the
two certified Effect steps, before reporting the remaining Value queue.

| Dispatch/block | Remaining Value queue |
|---|---|
| J_h/c_y; copy J_h -> J_h' | `[J_h/U_y,J_l/c_y,J_l/U_y,J_h'/c_y]` |
| J_h/U_y; Argument q1/A_h, Result H_h/z_y | `[J_l/c_y,J_l/U_y,J_h'/c_y,Int/A_h,I_h/z_y]` |
| J_l/c_y; copy J_l -> J_l' | `[J_l/U_y,J_h'/c_y,Int/A_h,I_h/z_y,J_l'/c_y]` |
| J_l/U_y | `[J_h'/c_y,Int/A_h,I_h/z_y,J_l'/c_y,Int/A_l,I_l/z_y]` |
| J_h'/c_y; Int/A_h; I_h/z_y | `[J_l'/c_y,Int/A_l,I_l/z_y,I_h/U_z]` |
| J_l'/c_y; Int/A_l; I_l/z_y | `[I_h/U_z,I_l/U_z]` |
| I_h/U_z; Argument q2/B_h, Result B_h/w_y | `[I_l/U_z,Int/B_h,b_h^-/w_y]` |
| I_l/U_z | `[Int/B_h,b_h^-/w_y,Int/B_l,b_l^-/w_y]` |
| Int/B_h | `[b_h^-/w_y,Int/B_l,b_l^-/w_y,Int/b_h^+,Int/w_y]` |
| b_h^-/w_y; Int/B_l | `[b_l^-/w_y,Int/b_h^+,Int/w_y,Int/b_l^+,Int/w_y]` |
| remaining primitive/row insertions | `[]` |

Equal endpoint tasks with different fibers retain their actual source sets;
duplicate/current checks may remove a repeated terminal step, never add a
new Parent or Value continuation to this table. Where an input slot has
more than one attached relation, the replay block expands that cell in its
actual newest-first fiber order; the table records the resulting Value
frontier shape, not a claim of numeric RelationIds or physical-slot counts.
No q1/q2 is replaced by Int
before its real bound replay. No H/z row Link is replaced by a structural
Function comparison.

Only three operations in this table and its initial chain allocate rows
before the first settlement. Here is their **complete** Parent order.
`parent^sign -> copy` denotes the actual Parent's endpoints, polarity and
target 1. Kind is explicit. No arrows in this table are solver Links.

| Group | Ordered Parents, all target 1 |
|---|---|
| x/U_p negative extrusion | `Value y+ -> c_y`; `Effect N_yp+ -> n_yp+`; `Effect I_p- -> i_p-`; `Value z_p- -> z_p-`; `Effect C_p- -> c_p-`; `Effect D- -> d-`; `Effect R_V- -> r_V-` |
| J_h/c_y positive extrusion | `Value A_h- -> a_h-`; `Effect E_Jh- -> e_Jh-`; `Effect R_Jh+ -> r_Jh+`; `Value H_h+ -> h_h+`; `Value B_h- -> b_h-`; `Effect E_Ih- -> e_Ih-`; `Effect R_Ih+ -> r_Ih+`; `Value B_h+ -> b_h+`; `Effect R_Ih- -> r_Ih-`; `Effect R_Jh- -> r_Jh-` |
| J_l/c_y positive extrusion | the same ten ordered entries with independent subscript l |

Thus there are 27 Parents: 10 Value and 17 Effect. All copies are fresh,
all parents are then level 2, and each source set contains an actual
qualifying self-call event. R256 supplies e_l1 for x/U_p; delta_h/delta_l
retain that event through the y/c_y link for both later groups. Each Parent
is appended to pending at creation (intrusion:306-364). Groups are activated
already; recapture cannot append them a second time (364-420). Earlier
source drains and k FreshUse restore only level-2 rows and allocate no
extrusion Parent. This list is the complete pending suffix from its entry
cursor, not one group's selected subset.

Inventory justification is by actual Visit-time snapshots, not entry graph
reachability alone. At x/U_p, y has no lower (EMPTY256); N_yp has only Bottom
as lower; I_p's negative selected upper spine is C_p,D,R_V. R_V has no upper
yet because D_h/D_l have not dispatched. z_p has no Value upper. The
StatementBlock body edges are direct (source:2115-2140); extra Group wrappers
would require their own listed rows and are outside this exact HIR subcase.

At J_i/c_y, A_i has no upper and H_i has its actual I_i lower. Neither
independent k_i has yet been compared with U_y, so E_Ji's negative selected
upper is R_Ji, and E_Ii's is R_Ii; before their own positive Visit each R
has only Bottom as a lower. Structural work finishes before pending selected
bound work. In particular **R_Ji+ and R_Ii+ are visited before their deferred
negative Visits through E_Ji-/E_Ii-**. Those negative Visits later see the
fresh positive-copy upper, but that copy is a level-1 anchor and adds no
Parent. B_i- similarly installs the lower b_i- before B_i+ snapshots its
lower lane; that later selected item is an anchor. This prevents both an
omitted sign and an invented extra Parent. h and l cannot cross through
these k rows: their fresh graphs are independent and closed, and the g
effect consumers do not enter either k's entry/return row before its own
comparison. Subsequent Effect work creates no copies; the remaining Value
table uses only target-2 insertions or target-1 anchors/primitives.

## 4. Why the actual ordinary queue reaches its first empty cut

This is a termination argument for this explicitly bounded pre-settlement
suffix, not R70 W or a whole-source drain theorem. It is needed in addition
to the projection. There are finitely many actual initial source/fresh rows,
the 27 listed copies, and finitely many original/copied structural terms in
the Value table. No step outside those three operations allocates an
endpoint. Let V be this finite endpoint inventory and S the seven actual
checking events `{e_y1,e_y2,e_p,e_h1,e_h2,e_l1,e_l2}`. Relations have only
pair in V, identity Context, default scoped flow and sources subset S;
therefore they have finitely many possible interned keys. This statement
retains the actual RelationIds and dependency lineage, not just their sets.

Within this interval generation never changes: settlement is called only
when the typed queue is empty (lib:14411-14416), and it is the only row-merge
owner. Admission marks `(actual processing relation,generation)` current
immediately (intrusion:423-454; lib:15445), before that dispatch can emit
replays or Function children. Consequently each canonical relation can
perform its bound/Function action at most once. Equal/current dispatches
emit no descendants. Each such action appends finitely many physical slots,
so all slot enumerations are finite. Attachment deduplicates the exact
`(BoundKey,RelationId)` (context:3702-3715); ordinary Replay emits a child
only for a novel dependency and excludes old/old products. Thus the total
number of emitted replay children is finite, including cyclic Effect paths
through D/R_V and both second-call consumers. A finite number of Value
Function admissions and rewrites emit finitely many additional queue items.
Replay acknowledgements add no tasks. There is no incoming-use restoration
inside this suffix which could request old dependency replay anew.

Every pop therefore consumes one of finitely many items, and every guard
on the Effect contraction has been decided in section 2. Front insertion
does not starve an existing item in a finite emitted word. At the first
Transport step whose current is absent after that finite word is consumed,
the *actual typed queue*, including all Effect items, is empty. This is not
an empty Value projection asserted to be the typed queue. Its pending suffix
is exactly the ordered list in section 3, because Effect dispatch has no
Parent constructor and the exhaustive Value table names every productive
extrusion. Finite transformer support on its own would not justify any of
these conclusions.

## 5. Apply SETTLE254, then the distinct row child and U_z

At this first actual empty cut apply SETTLE254/MIN254 to all 27 entries.
Each listed copy has entry level 1 and its original parent level 2; the
Value/Effect forests are disjoint. Therefore:

```text
mu(y)=mu(z_p)=1;
mu(A_i)=mu(H_i)=mu(B_i)=1, i=h,l;
mu(N_yp)=mu(I_p)=mu(C_p)=mu(D)=mu(R_V)=1;
mu(E_Ji)=mu(R_Ji)=mu(E_Ii)=mu(R_Ii)=1;
mu(z_y)=mu(w_y)=mu(q1)=mu(q2)=2.
```

Every omitted row is isolated in this Parent graph. In particular z_y is
not lowered merely because H_i/z_y is a Link or because Effect D is merged.
Copies redirect to their original parents at settlement, including both
signs of B_i and R_Ji/R_Ii. Genuine merges append both bound sides and
transport/canonicalize fibers before merged-lower replay; these are the
actual owners in intrusion:568-710 and context:4649-4673.

The merged y has its old J_h,J_l lowers and the transferred actual J_h',J_l'
lowers from c_y, as well as its old physical U_y upper. In particular the
transferred beta_cyh of R257 canonically attaches to `(y,+,J_h')` and retains
its sources; it is not replaced by an arbitrary new origin. That new key
and the actual `(y,-,U_y)` fiber have no prior ordinary replay head. Their
new/new product therefore emits `(J_h',U_y)` at the back. Its structural
lower was previously consumed only at c_y; there was no U_y upper there.
The original J_h/U_y may also replay; keep both. The structural root pairs
have identity Context/default flow; no raw-pair retained extrusion rewrite
exists for J_h'/U_y. Endpoints are structural roots, so canonicalization
does not change them.

Whether this or an earlier ordinary replay of J_h/U_y is processed first,
take the first current-generation Result child using either actual high
lower against U_y. Its actual child is

```text
(a,z_y), where a=rep(H_h)=rep(h_h+), level(a)=1,
level(z_y)=2.
```

This is a row pair, not a structural Function endpoint. Before settlement
the equal-level row pair was stored on H_h's upper lane. Now its dispatch
stores a **lower row a on z_y** (extrusion:1127-1138). No previous lower-row
key `(z_y,+,a)` existed: pre-settlement z_y had only structural I_h/I_l
lowers. The unchanged raw pair has no retained whole-pair extrusion rewrite;
its previous completion belongs to the old generation. If an earlier
current-generation Result has already processed it, that earlier occurrence
is the same desired producer, not grounds to suppress the existence claim.

Let gamma be its actual new attached lower fiber and upsilon the retained
upper fiber for `(z_y,-,U_z)`. Their novel ordered Replay dependency emits
`(a,U_z)` with source union and identity/default payload. This raw pair did
not execute before settlement: the earlier consumer was `(I_h,U_z)` with a
structural lower, not `(H_h,U_z)` with a row lower. Until its first dispatch
there is no whole-pair extrusion rewrite for it and no current-generation
completion; Context does not consume it. Earlier Effect items remain finite
and cannot change its Value endpoints. All k port rows are now anchors at 1,
so replaying their old structural lowers cannot create a new deep Value
copy before this first row/Function consumer.

The row/nonrow branch consequently extrudes **U_z negatively at a's current
level 1**. Its first Argument Visit is `(q2,+,1)`, with q2 still level 2;
its Result Visit is `(w_y,-,1)`, also still level 2. It thus creates new
productive copies/Parents. q2's selected Int lower has its original source
fiber; the operation is not just a relabeled old whole-pair rewrite. The
actual high first-call event e_h1, like e_l1 in R256, has origin
Local(g) and receiver Local(g); its own source Value is in the same sealed
SCC. Thus both an original high path and the transferred beta_cyh path
carry a qualifying event. The group is retained for later
intrusion. This is a finite productive successor after the complete first
settlement. No claim is made that its new full suffix drains, that the
process repeats uniformly, or that this gives divergence.

## 6. Scope, next evidence and stop

Reused within premises: EMPTY256 and source-owner chronology; SEED257's
actual FreshUse/lower/link fibers; STORE253/WAVE253; SETTLE254/MIN254 only
after the complete ordinary suffix calculation. Rejected: scoped collection
success assumed from a source-shaped sketch; failed private state reused as
ordinary state; introduction record equated with executable demand; identity
Context equated with default scope; a Value projection called a typed drain;
one sign's snapshot reused on the other; finite transformer support called
queue completion; slot equated with fiber; row Link equated with equality;
primitive literal row equated with its Int lower; birth levels substituted
for complete minima; structural I_h/U_z confused with row H_h/U_z.

The exact review-critical claim is `ORDINARY258-SUFFIX`: section 2's
small-step Effect contraction, section 3's exhaustive Value projection and
27-Parent order, section 4's finite actual emitted word and section 5's
first current-generation row child. A counterexample is a source-created
nondefault ordinary flow/nonidentity Context; an earlier incoming bound on
one isolated k return before its own copy; an additional Value/Effect Parent
in this exact HIR; or a preexisting `(z_y,+,H_h)` / `(H_h,U_z)` key before
settlement. Any such finding blocks the settlement/productive conclusion.

Mutual TODO `R258-REVIEW-SUFFIX-1`, owner Luna: assign a fresh independent
compiler_referee to these frozen bytes, especially the contraction versus
the contract's actual queue requirement, deferred signed snapshots,
source-mode distinction, all Parent groups and first row-child novelty.
If exact ordered fiber expansion rather than the proved contraction is
required, that unexpanded replay ledger remains explicit missing evidence;
it must not be silently described as a numeric full queue trace.

The full parent still requires R70 W, Q253 later-trigger bounds, R71
raw/canonical association coverage, evidence authenticity, diagnostics,
qualifying-intrusion adequacy, generalization, hygiene, all other accepted
source constructors, F1/FK1 and foreign continuations. This source route
does not discharge those independent quantifiers or the full proof.

Implementation **NO_SAFE_CODE_SLICE**. The inspected ordinary append/extrusion
and merge/replay owners establish no accepted-source violation of an approved
clause. The private scoped collector's explicit support guard is not evidence
of a production defect. No compiler or instrumentation TODO is proposed.

Three stages: (1) byte/source/mode gate; (2) ordinary transitions, signed
inventory and suffix contraction; (3) settlement/consumer application and
freeze. Maximum 2400 active seconds; full grant charged at admission, no
extension/refund/carryover. Final clock and hashes are in the exact inbox.
Only static reads/searches, SHA-256 and the two leased writes were used.
No Lean/build/test/probe/Cargo, scratch/cache, runtime/quarantined access,
production/shared-state edit, Git, external contact or descendants.
All new paths are this note and the exact R258 inbox; scratch none.
After the final hash receipt: **STOPPED / WRITES_STOPPED**, no background
work or unresolved descendant lease. Independent acceptance belongs to Luna.

# R255: forward source owners and the selected-lower snapshot barrier

Revision 3; freeze ID `R255-SOURCE-OWNER-COINCIDENCE/r3`. Source analysis by
`/root/sol_r255_source_coincidence`, requested `gpt-6.1-sol/high`; observed
model/effort UNKNOWN because the worker received no runtime metadata. Luna
made bounded wording corrections in response to r1/r2 review; no source
derivation, quantifier or conclusion changed. Candidate source-native
derivation and an exact remaining construction premise. **Neither a
source-wide exclusion nor an accepted counterexample.** Independent review
of revision 3 remains pending.

## Parent, application and outcome

The parent remains Yulang inference soundness and its Rust implementation,
with the original accepted source domain, Simple-sub A/B, independent
satisfying assignments, shared witnesses, F1/FK1 and foreign continuations.
The immediate application edge is R70-DRAIN-1 / D253 /
SOURCE254-COINCIDENCE. Use actual initialized successful finite prefixes;
no eventual drain return is assumed. Parent/A/B delta **0 to 0**.

The forward source audit identifies a parameter route which avoids R254's
separate-owner mistake. A parameter Name uses the actual parameter row, so
that row can both own an Apply upper and be selected positively as the
Argument of another Apply upper. A direct recursive source event can supply
the qualifying source identity on the proposed route. This is a constructor
map, **not** proof that the whole proposed execution is accepted or that
all its input fibers and guards exist. In particular no complete pending
suffix, unequal minima and productive consumer are certified together.

The first remaining construction equation is chronological: a suitable
structural lower must already belong to that same parameter's selected
physical prefix when its positive Visit takes the snapshot. Its copied
lower must then survive the complete settlement and the actual later replay.
A source program which merely gives that parameter a stale upper supplies
no such lower. The owner equation and this failure are applied below to
SOURCE254; no uniform multiplicity bound m is supplied.

Q253, R70 W, R71 association coverage, evidence authenticity, diagnostics,
qualifying-intrusion adequacy, generalization/hygiene, F1/FK1, foreign
continuations and full soundness stay separately OPEN. There is no evidence
of divergence, a production defect or a semantic need for global sharing.
Implementation disposition: **NO_SAFE_CODE_SLICE**.

## Gate, authority and immutable inputs

Initial gate at `2026-11-02T05:56:27.085921Z`: read-only filesystem
`.git/HEAD`/ref resolution gave exactly
`6336a19fd4543ae25933f985df45d3a14b5fb648`. All **36/36** contract SHA-256
pins matched before any pinned body was opened or cited. The receipt was
sent to Luna before further source work. No Git command was run.

Contract `tasks/agent-loop/sprints/source-owner-coincidence-r255.md`,
SHA-256 `f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`.
The exact 36 path/hash pairs in that contract are the dependency manifest;
the final gate rechecks every pair, rather than selecting only cited files.
R254 note hash `5c7d3059005dc03be58fde7528519b9d47674c80cedf48d48983c29242fe1bce`;
R253 note hash `15458a226a3949e67b747540b1279dd054f1e280418c5746610bda4ce2933655`.
Their respective authors are `/root/sol_r254_opposite_leaf` and
`/root/sol_r253_receiver_ancestry`. Source files retain repository authorship.
This worker claims authorship only of these two R255 outputs.

After the gate, Luna reported admin checkpoint
`48d57475f66727e033c19223a6d298f23afced78`. Luna's exact reconciliation says
the diff from the admitted baseline contains only
`tasks/agent-loop/current.json`, the R255 admission history and the R255
contract, with every pinned byte unchanged. This is primary-owned Git
evidence, not an independent commit-object audit by this worker. The final
filesystem ref and all pins are checked again in the inbox receipt.

Governing authority: root operating map, rules/goal-driven-sprints.md,
assigned contract/admission and the Authoritative inference top-level
principles. The sprint and proof-portfolio skills were read and applied to
parent attachment and finite leases. The Lean skill's claim/checking
boundary was read; no Lean work was assigned or performed, and there are
no Lean declarations, kernel theorem types or axiom-audit claims.

## 1. A relation-preserving source-owner ledger

For an actual row r, keep one record indexed by its current canonical row:

```
(kind, raw members, current representative, current level,
 physical slots [raw owner, lane, index, endpoint, emission],
 attached fibers [complete BoundKey, RelationId],
 actual selected Visits [occurrence, sign, target, snapshot, source set],
 pending Parent indices and complete component/minimum,
 later ordered replay inputs, dependencies, ports and consumer tasks).
```

An equality of semantic Values in the reference graph is not row equality.
A directional row bound is not row equality. A physical slot is not an
attached executable fiber. Historical structural terms retain their raw
children even when their top-level owner keys are canonicalized. Thus a
ledger may have several original physical owners after a merge; each
transported destination slot and its attached fibers must be recorded.

The following are forward constructor equations from the pinned bodies.
They preserve these distinctions; they do not assert closure of all source
constructors or establish R71's missing correspondence.

| Source action | Actual Value endpoint / physical structural owner |
|---|---|
| Parameter Name | Endpoint is `Parameter(position)` for that resolved parameter, shared across its Names; it is not the Name's allocated component. |
| Active local Name | Endpoint is its own component; `Link(initializer, Name)` admits a directional Value constraint. |
| Group / block final value | Own component and a Group recipe from the child's endpoint; neither aliases the child merely by source spelling. |
| Sequence / If / Case / Catch result | Own component; designated child endpoints admit directed Value constraints into it. An If without else returns Unit. |
| Ascription | Planning aliases the canonical peeled child endpoint; this explicit alias is distinct from an ordinary Group facade. |
| Apply | Upper Function is admitted against its actual callee endpoint. Argument is its actual endpoint; Result is its own application ValueRow. |
| Lambda | Lower Function is admitted into its root component. Argument is its selected formal domain (the parameter row on the named-formal route); Result is its exact body endpoint, including any block/sequence facade. |

Owners: candidate_source.rs:1080-1169,1220-1380,1547-1584,
1605-1720,1794-1803,1908-1924,2078-2140,2482-2494;
shadow_apply.rs:4302-4400; lib.rs:11620-11821.
The represented HIR forms and statement distinction are explicit at
local_source.rs:333-440. No assumption about an invented Lambda syntax or
rewriting a named formal into an arbitrary endpoint is used.

In particular, for equal-level row/row `(a,b)`, actual bound application
stores `b` on `a`'s upper lane; for a strictly lower a and higher b it stores
a on b's lower lane. Neither operation merges a and b
(candidate_extrusion.rs:1115-1138). Source actions drain sequentially;
settlement occurs only after the typed queue is empty
(lib.rs:14411-14446). Actual equality is separately owned by the qualified
Parent settlement, not by the source Link recipe.

For settlement, reuse SETTLE254 with its exact successful-call premises:
build the graph from **every** entry-representative Parent in the complete
pending suffix, preserving both kinds/signs/groups/activations. If C(v) is
the component and mu(v) its minimum entry level, then

```
rep_after(v)=rep_after(w) iff C(v)=C(w);
level_after(rep_after(v))=mu(v).
```

Consequently the stale opposite leaf test is exactly `mu(s)>mu(r)`, not
absence from one sign's local traversal. merge_candidate_rows appends both
sides, transports origins/fibers, takes the minimum and replays every merged
lower (intrusion:599-710). This applies the ledger to the original D253 edge;
it does not replace the Parent provenance with the reference SCC graph.

## 2. Parameter route: where positive and negative selection differ

First reject the tempting one-formal self-argument route. If a high formal
y has lower Lambda Function T whose Argument is y itself, then a positive
Visit of y at target L selects T and visits its Argument negatively at L.
That negative Visit selects y's upper Function U, including U's Result leaf.
When all those Parents belong to the activated suffix, MIN254 includes them;
one cannot declare U's leaf untouched because the outer Visit was positive.
This is a local rejection under those exact selected-prefix premises, not a
source-wide theorem.

The two-formal route avoids that particular negative revisit. Consider the
following **unexecuted source-shaped construction input**, not an accepted
prefix or countertrace:

```yu
my outer x = {
  my g p y = { y 0 0; p y; g x };
  g
}
```

Use named source identities, not freely chosen solver terms. Planning puts
outer parameter x at 1 and g's initializer, p, y and body at 2. g has an
outer Lambda root G with Result the distinct inner Lambda root H; H has
Argument y and Result the distinct block b. The last `g x` has application
Result z_q, with a later directed Group constraint `z_q <: b`. In `y 0 0`,
the first Apply's Result z_y is the second Apply's actual callee; inserting
an explicit Group would introduce another owner and must be tracked.

The candidate ledger, before any alleged equality, is:

| Row | Structural slot / link to track | Selected role and settlement debt |
|---|---|---|
| y_2 | upper U_y=`F-(i_y,...,z_y)` from first `y 0` | proposed positive Visit at 1; U_y is on this very row |
| z_y,2 | upper U_z=`F-(i_z,...,w)` from second Apply | distinct later consumer owner; never identify it with y |
| p_2 | upper U_p=`F-(y,...,z_p)` from `p y` | proposed low-row replay operand; its Result is z_p, not z_y |
| G_2 | lower T=`F+(p,...,H)` only after outer Lambda action | active Name links to each recursive Name component |
| n_q,2 | upper U_q=`F-(x,...,z_q)` from `g x` | has its own root-to-Name Link, not identity with G |
| H_2 | lower V=`F+(y,...,b)` after inner Lambda action | root H is distinct from b and z_q |
| b_2 | final-value Group from z_q | no structural U_y slot is silently moved here |

Each structural slot still needs its real emission/fiber and later canonical
transport; the table deliberately supplies none by fiat. It is an owner
map for a candidate input, not a fabricated physical execution certificate.

The event of `g x` has origin Local(g) and receiver Local(g), whereas `p y`
and `y 0` have parameter receivers. The reference producer retains precisely
the Apply checking occurrence at slot 0 and seals equal-planning-level SCCs
(value_graph:332-397). This explains why the *g event*, if present in the
processing source union, qualifies; it does not qualify the p/y events by
association or replace the required processing fiber. Active recursion emits
G-to-n_q Link, then ordinary replay can compare T with U_q. The actual
Function.Argument child is `x <: p`; at levels 1 and 2 its insertion is a
lower x on p. Replay against U_p then proposes `x <: U_p`.

The negative traversal of U_p at target 1 visits its Argument y **positively**
and its Result z_p negatively. A deep positive y Visit takes only y's lower
prefix; it does not thereby visit U_y or z_y. Thus this local selected path
can emit Parent(y_1,y,+,1) while the separate U_y is on the same raw owner.
It also emits the actual Effect/Result Parents required by U_p; they cannot
be dropped. The first simple one-formal negative-revisit argument therefore
does not establish a global exclusion for the two-formal owner map.

This is the precise limit of the derivation. To certify the proposed path,
one must supply its actual input fibers and ordered dependencies, Context
and memo admission, all coactivated Parents and the complete mu values.
Other selected lowers of y and other Parents may reach z_y. Neither
`mu(z_y)=2` nor `mu(y)=1` is asserted for an actual complete execution here.
No parser/solver execution established acceptance of the displayed input.

## 3. The first consumer barrier is a selected-prefix timing equation

The two-formal input has no source constructor which simply installs a
positive Function lower on y before the proposed Visit. Its stale upper
alone cannot trigger a productive child. The positive Visit snapshots direct
and exact lower lengths **before** attaching its source link; Work::Bound
copies only that snapshot (extrusion:96-185,395-412). Selected-bound
initialization is not ordinary replay of every old opposite slot.

For the mapped-lower consumer route, the first missing equation is:

```
SNAPSHOT255(y,o,T):
  before Visit(y,+,L) of the actual qualified occurrence/group o,
  a particular physical positive structural lower T of rep(y)
  and its executable input RelationId are already in that Visit's prefix;
  its selected copy T' is installed on y's actual copy with transported fiber;
  after the complete suffix, y and a selected T' leaf a have the required
  actual representatives/levels while mu(z_y)>mu(y);
  merge replay selects the transported T' and retained U_y fibers.
```

This is a missing equation, not a new assumed invariant or completed theorem.
Owning producers: source actions for recursive arguments and Lambda facts,
candidate_step_function_dispatch (lib:15059-15089), candidate_apply_value,
and the Visit/Work::Bound constructors. Owning consumer: merge_candidate_rows
and candidate_replay_bound. Another route need not satisfy SNAPSHOT255, but
must identify its own actual lower/replay trigger; this packet proves no
necessity theorem over all possible renewal mechanisms.

A related construction attempt adds an earlier high self-call `g p k` and
a later low self-call `g x k`, with k intended to supply the lower Function.
This is still unaccepted and incomplete. Each recursive Name, intermediate
Apply and optional Group has its own row. The first call must actually
propagate through G-to-Name, Function.Result to H's result receiver, the
second Function.Argument, k's own row and its lower before the low call's
`x <: U_p` Visit snapshots y. Merely putting that call earlier in source
text does not prove that inequality of queue events.

The actual queue facts constrain this attempt: bound replay transfers children
to the **back** without dispatching them; Function children are admitted in
reverse order and pushed to the **front**, so their execution order starts
with Argument (context:4598-4647; lib:14905-14947,15059-15089,15328-15348).
All queued work precedes settlement. A structural lower which arrives after
the snapshot may exist at merge, but it is not retroactively included in the
copy's selected prefix. A later ordinary insertion at the lowered receiver
must itself extrude at the receiver's current level. No timing certificate
for the proposed seed is supplied, and no impossibility of all seeds follows.

Even with SNAPSHOT255, the ordinary named-formal route used by the displayed
candidate compares the Apply argument row with the Lambda parameter row, and
the Function Result compares the Lambda body endpoint with the Apply Result
ValueRow (lib:11620-11650; shadow_apply:4310-4316; lib:14905-14947). That is a
candidate-local fact, not a rule for every accepted Lambda form: Lambda
construction can retain a structural formal domain, including a Record
domain for a record pattern or Unit for a unit pattern
(lib:11630-11633; effect:2094-2100,2112-2118). Such forms can present a
structural argument endpoint and require their own exact row/nonrow consumer
analysis. This correction preserves the full accepted source domain and does
not claim those routes close SOURCE254. The displayed candidate uses named
formals `p` and `y`. For its immediate port, the row children remain rows;
the result child `(a,z_y)` still needs its actual row-bound insertion/replay
against U_z to reach a full pair such as `(a,U_z)` at a's current level.
This keeps the intermediate owner `z_y` and its fibers; it cannot be
compressed to a structural Result on y.

The remaining checks are executable premises, not consequences of a high
leaf: exact replay quadrants/new dependency (context:4411-4497), Transport
and Context before memo (context:4186-4258; lib:14411-14474), post-check
Function port with Swap/Preserve and actual scoped flow (context:3924-3988),
current-pair/canonical alias/retained full-pair rewrite guards
(lib:14565-14615,15380-15398), and the actual row/nonrow dispatch at its
current representative level (lib:14814-14866). A generation change does
not clear a retained extrusion rewrite. No novel productive pair has been
certified through those guards in R255.

## 4. Reuse, mutual TODOs and bounded stop

Reused R254 SETTLE254/MIN254 only for successful complete fixed suffixes;
R253 STORE253 only for actual ordinary structural insertions and WAVE253
only for one captured replay invocation. R70's local simulation remains
conditional on W. R250/R251/R252's conditional entry-only bounds are not
applied without the still-missing multiplicity premise. Rejected: Links as
equalities, collapsed Lambda/body/Apply owners, qualification from a source
label alone, raw birth levels as final levels, and a later lower as though it
had belonged to an earlier selected prefix.

First remaining task for Luna's next admitted source lane:
`R255-SELECTED-LOWER-1` — settle the actual chronological construction of
SNAPSHOT255 or give a different complete accepted owner/replay certificate.
Falsifier of any exclusion: one accepted finite prefix retaining the exact
same-owner slot, attached fibers, qualified Visit/group, complete unequal
component minima and a later novel productive child after every guard.
Falsifier of the displayed seed attempt: the structural lower's first actual
insertion occurs after the positive Visit snapshot, or its required consumer
is already current/rewritten/without a novel Replay dependency.

Mutual TODO: Luna supplies admission/review/integration and any future exact
source-input/provisional-execution lease; a future producer supplies an
actual source-owned chronology, not an assumed transition test. No new lease,
semantics, dependency, test or instrumentation was created here. Inspection
of candidate_extrusion's insertion and candidate_intrusion's merge/replay
owners yields no accepted-source violation of an approved clause, hence
NO_SAFE_CODE_SLICE; production edits remain unauthorized.

Three substantive stages only: (1) baseline/pins and forward owner map;
(2) one-formal rejection, two-formal route and chronological seed audit;
(3) application at SOURCE254 and exact-obstruction freeze. Full 2400-second
grant charged, no refund/carryover/extension. Actual active CPU/provider time
and RSS UNKNOWN; elapsed observable span is reported in the inbox. Only
static reads/searches, filesystem ref resolution, SHA-256 and these two
leased artifact writes were performed. No builds/tests/Lean/probes/Cargo,
Git, scratch/cache/runtime/quarantined writes or reads, production/shared
state/config/test/expectation edits, external contact or descendants.

Only new/written paths are this note and
`tasks/agent-loop/inbox/source-owner-coincidence-r255.md`.
After the final hash receipt the author is **STOPPED / WRITES_STOPPED**.
No descendants or outstanding writer leases exist outside those exact paths.
Fresh independent review is NOT_RUN by this producer; no self-certification.

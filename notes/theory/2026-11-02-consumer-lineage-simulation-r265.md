# R265: consumer-derived temporal lineage obligation

Revision 1. Candidate source/native evidence; simulation and original parent OPEN.
Sole author `/root/sol_r265_consumer_lineage_51dd6af`; no descendants or coauthors.
Contract `tasks/agent-loop/sprints/consumer-lineage-simulation-r265.md`, revision 1,
SHA-256 `2062a88a9ce130155bf794683325c942dd1dca3cd79b9fccf845bb23e12e0237`.

## Parent and actual result

The unchanged application edge is inference soundness -> R70 copy correspondence
-> `R71-RAW-CANONICAL-FIBER-COVERAGE-1`. Preserve the original accepted source
domain, Simple-sub A/B, independent satisfying assignments, shared witnesses,
F1/FK1, and foreign continuations. This packet neither restricts those quantifiers
nor establishes their concrete source instance. Parent/A/B delta is **0 -> 0**.

The result is a backward derivation from the production replay/Function-port
consumer, a time-indexed inventory of the actual transport constructors, and an
explicit unresolved temporal equation. It is not a completed simulation, a
source-qualified counterexample, or an independently reviewed theorem. There is
no concrete accepted-source history here that demands a missing canonical fiber.
There is also no proof that every source-required lineage has an actual covering
path. The constructor formulas below identify the first missing comparison rather
than assume it as a new theorem hypothesis and report success.

Use R70 and reviewed R71 only within their successful local-construction premises.
The successful-forward domain used by reviewed R261/R262 supplies useful physical
and replay facts there; it does not discharge all permitted-history, abnormal
continuation, rollback, or general ENTRY-WF premises of the unchanged parent.
Lean declaration/type/axiom audit: NOT APPLICABLE. No Lean/checker was run.

## 1. Actual consumer and its source spine

The executable consumer selected for this audit is
`lib.rs:15060` `candidate_step_function_dispatch` ->
`candidate_context.rs:3924` `candidate_function_port_admit`, after an actual
replay child reaches typed-drain Transport, Context, Dispatch and FunctionAdmission
(`lib.rs:14411-14485`). This names a production consumer site and derives its
requirement for any reached instance; it does not claim that a particular
source expression with a preceding alias reaches it.

Source Apply construction retains the actual callee, argument, application result
and effects, original occurrence and call index (`candidate_source.rs:1808-1924`).
`shadow_apply.rs:4302-4377` builds the negative Function demand from the actual
argument, argument effect, fresh invocation effect and result, and retains its
native/source registration before admitting the constraint. An Apply result is
its own endpoint; this construction does not identify it with a Lambda body or
definition root. `candidate_context_seed:3791-3838` associates an eligible scoped
checking occurrence with `ScopedDemand { original_call, use_instance:0, root,
output_scope, input }`. Eligibility is guarded by the retained introduction;
this audit does not assume every Apply has one. The same source seed owns the
source-event set; occurrence qualification remains the approved source Value
SCC operation, not solver-row SCC membership.

For an ordinary replay, `candidate_replay_bound` canonicalizes the physical
owner and both selected endpoints and supplies the ordered lower/upper BoundKeys
(`candidate_extrusion.rs:1070-1111`). `candidate_context_begin_replay:4411-4497`
reads the exact two linked fiber lists. It enumerates new-lower x all-upper and
old-lower x new-upper quadrants; incoming-use replay instead starts from empty
prior heads. It retains each exact

```text
Replay { child:q, lower:l, upper:h, lower_input:bL, upper_input:bU }
```

and its evidence recipe. Equal child IDs do not identify different input records.
Ordinary exact dependency novelty can suppress another queue admission; incoming
use has its explicit diagnostic ownership rule. Retained operation/vector,
queue transfer, execution and acknowledgement remain separate.

Write `K(r)` for immutable `relation.key.context`, `S(r)` for its retained source
set, and `F(r)` for its scoped flow. The replay child is constructed from

```text
K(q) = J(K(l), K(h))
S(q) = union(S(l), S(h))
F(q).transformer = compose(F(l).transformer, F(h).transformer)
F(q).demand = F(h).demand, with F(l).demand = None.
```

Here `J(I,I)=I`; otherwise `J(a,b)` interns ordered `ContextExpr::Replay`.
Composition is the actual `first.then(second)` in `compose_scopes:2970-2981`.
Importantly, replay reads **K**, not the parents' current post-check contexts.
An ancestry argument using only endpoint equality has not supplied this recipe.

The typed drain transports q to its canonical task identity before Context
execution (`candidate_context_transport_task:4186-4204`), retaining Derived if
that identity changes. Context execution records observations for actual Effect
operands and validates the live context fragment. At a reached Function port,
the exact current processing RelationId is the parent. Its post-check context
is inherited, Swap applies to Argument and ArgumentEffect, and Preserve applies
to ResultEffect and Result; a child-local closed Allowance prefix is added in
source order (`candidate_function_port_admit:3924-3988`). A demand requires the
parent's actual upper NegativeFunction root to equal `demand.root`. The demand
then disappears from the child: ArgumentEffect receives stamp_input(input),
ResultEffect protect_body(output_scope,input), and Value ports transformer 0.
The exact FunctionPort dependency records parent, child, field and operation.

Thus the consumer requires its actual ordered Replay incidence, canonical-task
transport, processing identity, authentic demand root and scope operation, and
the context remaining at that exact relation. It does **not** directly request
every RelationId in some earlier canonical bucket. Showing an additional
canonical fiber is independently required still needs the source-occurrence
correspondence, not an inference from bucket membership.

## 2. Timed constructors and proof-relevant inventory

Let H be an actual finite source history; time labels below are proof indices of
its events, not new runtime fields. Let

```text
P_t(r) = discharge_residuals_t[r] (or I) if r is discharged at t;
         K(r) otherwise.
```

This is exactly `post_check_context:3716-3720`. Residual/discharged entries are
indexed by RelationId, not by canonical pair. `execute_relation:4219-4307`
validates the context's zero-word filters, performs the actual Allowance checks
or registration/replay callbacks, and then publishes that relation's residual
and discharge record. `candidate_zero_word_filters:4089-4178` preserves directed
operations, rejects invalid/buried filter fragments and the unsupported mix of
replay filters with directed residuals, and reduces replay-only filter residual
to I. Successful endpoint checks do not create a discharge entry for every
other relation at equal endpoints.

For any actual non-FreshUse witnessed transport r -> x at time t,
`candidate_context_transport_witness_with_evidence:4737-4751` supplies

```text
K(x) = P_t(r); S(x) = S(r);
F(x) = transported_scoped(F(r), exact from/to witness).
```

It retains the exact Transport dependency and FiberTransform, then attaches x
at the destination. The transform contains antecedent snapshot, from/to keys,
source/child RelationIds, reason and inherited coverage. The snapshot freezes
the actual source evidence heads and gaps (`context:845-863,953-980`). A bare
`transform_children[child]` lookup is not an enumeration of every transform:
the vector/key inventory retains distinct transforms even when that index is
advanced by another construction. No destination admission/emission is inferred
from this inert transform association alone. Source sets, metadata origins,
physical emissions and executable fibers remain distinct inventories.

`transported_scoped:3286-3298` preserves scoped data except its explicitly
witnessed NegativeFunction demand-root remap. For an Effect lineage its scoped
flow therefore remains exact through EqualityCanonicalization, ParentCopy and
Extrusion; no demand/provider/scope identities are collapsed. On a direct
negative Function item, the witness remaps a matching demand root to the actual
copied Function. This local fact does not prove authenticity for every indirect
row-link route reaching the Function consumer.

FreshUse has a different equation and must retain its independent use identity.
Preparation collects `P_a(parent)` roots and constructs the shared context/view
rename (`scheme:4694-4727`), while restoring a particular bound later reads
`P_b(parent)` again and looks it up in that retained map
(`scheme:4947-4995`). On successful restoration the actual looked-up entry
exists; success alone does not show `P_a(parent)=P_b(parent)`. Its child context
is that map's value, its flow is the retained shared scoped remap
(`scheme:4859-4883`), and Transport keeps exact FreshUse from/to, source parent
and nonzero use origin (`context:4697-4710`). Physical restoration separately
validates/reuses that relation (`context:4677-4695`). Freshening itself creates
no extrusion Parent. This audit does not substitute the ordinary transport
formula for the FreshUse rename.

For copying occurrence omega, each deep-row Visit snapshots both selected
direct and exact lengths before its opposite-side source link and schedules
**every** selected index (`extrusion:110-180`). For slot s, it retains raw
`k_s=(visited_owner,p,stored_item)` while visiting the canonical child key.
`Work::Bound:399-417` installs the selected physical image, then calls
`candidate_transfer_bound_origins:1045-1089`. That loop captures the exact raw
head, saves next before each transport, and covers the entire retained prefix.
Duplicate physical slots are scheduled; a shared bound key may have several
fibers, while duplicate attachment of the same RelationId is deduplicated.
Origin metadata with relation None does not add a scoped executable fiber.
Unscoped copied bootstrap may add an ordinary owner-derived relation in addition
to the exact source transports (`extrusion:619-633; effect:890-911`).

Prior/later merge paths cannot be omitted from a candidate inventory.
`merge_candidate_rows:599-710` transfers both sides using canonicalized item
lookup **before** changing the representative. Its subsequent whole bound-entry
sweep (`context:4649-4669`) forwards every captured changed key, preserves old
entries through attachment chains, and then merge replay uses the retained
parent's current bounds. The earlier completed sweep, not this later sweep,
justifies a merge's earlier canonicalized lookup. In contrast Work::Bound uses
its saved raw item. Neither owner reverse-saturates stale raw buckets.

Consequently a source-qualified absence claim must enumerate, for the actual
omega and consumer cut, all same-class selected slots, each raw prefix at its
transfer time, incoming-Allowance paths where present, unscoped bootstrap,
and every permitted intervening ParentCopy/canonicalization attachment path.
Each path carries its own dependency/transform/evidence history; one preferred
slot or one latest-child index is insufficient. This is the required inventory
algorithm over an actual finite history, not a claim that this packet constructed
such a history or a total source-wide covering map.

## 3. Attempted temporal square and exact obstruction

Fix an actual raw fiber r at selected raw key k. Suppose a prior successful
equality event e created canonical c from r, with retained transform E and
`K(c)=P_e(r)`. At copying time t the actual raw branch creates x, with transform
X, `K(x)=P_t(r)`. A copy *from c*, if an actual candidate path supplies it,
would create y with `K(y)=P_t(c)`. Retaining the fork (r,c,x,E,X) is valid
proof-relevant source evidence; it is not a c -> x Transport edge.

The consumer-derived context comparison is already nontrivial before ports:

```text
J(P_t(r), K(h))  ?~  J(P_t(c), K(h_c))                 (TEMP265)
```

Here h/h_c must be the actual opposite inputs of the two candidate paths;
their sources, flows, exact input keys and ordered Replay dependencies must
also correspond. `?~` denotes the unresolved comparison needed to preserve
the actual receiver checks and residual operations; no new semantic equivalence
is defined or assumed by this notation. Literal ContextId equality would be
a sufficient stronger route, but neither it nor the necessary consumer
comparison is established here.

One explicit, stronger equation attempted at the executor owner is

```text
Z_A(J(P_t(r), K(h))) = Z_A(J(P_t(c), K(h_c))),          (Z265)
```

where `Z_A(C)` means the actual validated `(filters, residual)` selected by
`candidate_zero_word_filters` in the fixed live Context/view arena A, before
its consumer callback, assuming successful reservations/sampling on that
call. It includes the actual ordered filter IDs and exact residual ContextId;
an error is recorded separately. Even Z265 has not been derived. Its failure
would not itself refute the parent: equality of this implementation-level
observation is a sufficient comparison route, and a weaker justified semantic
simulation could suffice. The required subsequent evidence is the actual
callbacks at the copied lower endpoint and both replay children's own
`P_v(q)` observations, not an assumed synchronization of their discharge maps.

After replay, the comparison must continue through each actual task transport,
Context execution and `P_v(q)` at the Function port. Replacing TEMP265 with
`P_t(r)=P_t(c)` still leaves those exact replay and child-residual steps to
justify. Conversely an unequal pair of ContextIds alone is not a falsifier:
the actual filter checks and remaining operations can agree. The source code
does not equate r's and c's discharge maps. A schematic event in which one
is discharged and the other is not illustrates the missing induction case;
it is not asserted reachable from accepted source.

Method 1 constructed the timed transport fork and propagated its immutable
payloads backward from the consumer. It preserves exact source/scoped data
for a fixed Effect lineage, but does not prove TEMP265 or select the required
canonical lineage for omega. Method 2 inspected the executor's normalization
and discharge owner. It identifies the exact filter/residual observations
that a proposed square must preserve; no rule there synchronizes distinct
RelationIds. The identity-context subcase trivially removes the scalar
comparison, but no all-source identity-context induction was established and
Effect contexts cannot be erased. These attempts do not yield a completed
or renamed conditional simulation theorem.

The first unresolved evidence is therefore a **source-reachable join** of an
actual selected occurrence, its canonical candidate and its named replay/port
consumer, with all candidate paths retained, together with TEMP265 and the
subsequent relation-local execution comparison. No accepted-source demanded
lineage was shown absent from every actual transport. No code repair follows.

## 4. Application at R70 and next evidence

Apply the formulas at R70's exact Work::Bound seam: the reviewed raw-prefix
transport fact now feeds the actual ordered replay recipe and the actual
Function-port inheritance formula above. This explains precisely what R70's
returned copied slot provides: actual raw-parent Transport/FiberTransform,
source/scoped payload and sampled context, followed by consumer-owned replay
and execution. It does not replace that raw parent with a canonical descendant
or discharge R71 coverage. The unchanged R70 copy edge remains OPEN at the
source-reachable join and TEMP265; general ENTRY-WF, later drain/eventual
Diagnostics, Q262-EPISODE, permitted-history/rollback, diagnostic adequacy,
successful-helper coverage, full soundness, A/B, F1/FK1 and foreign continuations
remain independently OPEN.

Mutual TODO `R265-CONSUMER-SQUARE-1` to Luna: retain parent R71/R70. Required
inputs are one actual source-generated occurrence omega, full selected physical
prefix and levels, qualification/Parent identities, raw/canonical keys, E/X and
all competing transforms, exact opposite replay inputs, and r/c/q discharge
cuts. Owners are `candidate_source`/`shadow_apply` source admission,
`candidate_extrude::Work::Bound`, FreshUse restoration, `merge_candidate_rows`,
`candidate_context_begin_replay`, `candidate_context_execute_relation` and
`candidate_function_port_admit`. Required output is a source-corresponding
consumer square, or the complete accepted-source missing-lineage witness.
Exact falsifier: that named reached consumer requires a source lineage with
no matching retained path after every same-class selected slot and permitted
merge path is accounted for. Unequal buckets, a hand-installed state, a local
frame or a source-shaped sketch do not meet it. This TODO grants no new lease,
source dependency, observer, test or semantic rule.

`NO_SAFE_CODE_SLICE`: the inspected extrusion/raw transfer and Context replay/
execution owners expose an unproved correspondence, not an established approved
clause violation. If Luna later grants a provisional observer, its minimal
requested records are exactly the input tuple above at the first source join
and named consumer; its falsifier must remain source-reachable missing lineage,
not simply unequal context IDs. No production change is proposed here.

## 5. Provenance, checks and freeze boundary

Reused: R70's local successful worklist/mutation/port facts; R71's reviewed
one-way raw retention and canonical forwarding, including its corrected head
retention wording; reviewed R261's nonemptiness/reference facts only within its
domain; R262's separation of birth/settlement progress from eventual drain.
Rejected as closure: raw/canonical fiber-set equality, endpoint-only ancestry,
nonempty fibers as complete coverage, metadata as executable lineage, one local
frame as F1/FK1/foreign-continuation closure, and assuming discharge synchronization.
No R230, quarantined R261 handoff, or R263/R264 output was read or used.

Direct dependency authority is the R255 manifest SHA-256
`f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`,
which authenticates all 36 exact pins, plus the ten exact governing dependency
hashes in the R265 contract. All matched before initial source reads, again
on resume, and at freeze as recorded by the handoff. Baseline
`51dd6af4e6a9cdfc305cecb825cb114d7b7e47ba` association is Luna's contract
authority; this worker hashed current bytes and performed no Git operation.
Prior authors: R70 `/root/r70_ordinary_extrusion_proof` with complementary
`/root/r70_extrusion_countertrace`; R71 `/root/r71_raw_canonical_proof`;
R261 `/root/sol_r261_diagnostic_reference_closure`; R262
`/root/sol_r262_source_wide_drain_progress`. Review/adjudication remains with
Luna and fresh independent reviewers, not this producer.

The pre-interrupt session stopped without any output write. Literal cfg(test)
path declarations inside the authorized pinned Context file were surfaced;
Luna adjudicated that this was not unpinned-source exposure. No referenced
unpinned file was opened. Resume revalidated every pin; no budget/stage reset
occurred. The 74-second pre-interrupt interval remains charged.

Requested model/effort Sol/high; observed model/effort and runtime session ID
UNKNOWN. Three stages: consumer derivation, timed-path/executor attempts,
parent application/freeze. Total grant 1200 active seconds; no expansion,
descendants, tests, builds, Lean, probes, Cargo, source edits, scratch/cache,
runtime/quarantined reads, Git or external contact. All new paths are only
this theory and `tasks/agent-loop/inbox/consumer-lineage-simulation-r265.md`.
Final hashes, measured clock envelope and actual writer-stop receipt are in
the frozen handoff and terminal return. Review/production status remains pending.

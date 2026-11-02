# R245: current native extrusion entry and return

Status: **candidate source-native evidence; entry bridge OPEN**. Revision 1.
Author: `/root/sol_r245_entry_return`; no descendants or coauthors.
Contract: `ordinary-extrusion-native-entry-r245`, SHA-256
`d79236d7b5e13b739c24e45b728f7b55db19eceebc5effce83e61b8e81555e61`.
Declared baseline HEAD: `5e228036817f6d1afe4271712dd6942790f26094`.
No Git command was run; the baseline is the contract's declaration, not an
independently observed HEAD. Current source claims use the verified byte pins.

## Parent, result and claim types

The unchanged parent is Yulang inference soundness and its Rust implementation,
with the original accepted source domain, Simple-sub A/B, shared witnesses and
arbitrary independent satisfying assignments. This packet neither chooses a
solution nor changes a quantifier. The parent locator is R70 §1 and the R245
contract; no fully quantified concrete full-inference Lean declaration occurs
in these inputs. This note does not invent one. F1/FK1, foreign continuations,
source/evaluator soundness, hygiene, qualifying intrusion and generalization
are not consequences of this local argument.

The exact edge is `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1`, with entry subedge
`R70-ENTRY-WF-1`. **Parent delta zero.** A constructor subpremise is removed:
`R244-NATIVE-PARAMETER-1` follows from the newly admitted owner and is applied
below at initialization. The full entry conjunction is not derived, and the
current return account remains conditional. No source-qualified malformed
prefix, code defect, production promotion or whole-language proof is claimed.

Informal types of the actual results, not Lean declarations:

```text
(D-PARAM)
For every formal registration accepted by initialize_candidate_source_levels,
let p = registration.recipe_position and q = parameter_live_base + p.
If its candidate_endpoint(Parameter(p), Positive) returns Ok(t),
  term_view(t) = LiveVariable(Value, Positive, q), q < bounds.len(),
  value_endpoint(t, Positive) = canonical_value(ValueRow(q));
  previously visible terms and allocated rows remain valid at this point.

(C-ENTRY)
For each actual call c in {call+, call-},
  ReachCurrent(c) AND [remaining construction/lifetime premises in §3]
  => WCurrent(c).
The bracketed premises are OPEN, not inferred from ReachCurrent.

(C-RETURN)
For every actual current invocation (sigma, root, p, L),
  CallerEnvelopeCurrent AND WCurrent(sigma, root, p, L)
  AND successful checked helpers
  => the finite operation-local map/snapshot/continuation/retention/queue
     postconditions in §§4–5.
```

`WCurrent` here means R70's storage-admissibility groups with **all** current
Function/Tuple/Record/Variant children represented. It is not a replacement
semantics or an assumed interface presented as a completed proof. These are
static source arguments awaiting fresh review. Lean declaration/type/axiom
audit: NOT APPLICABLE; checker NOT RUN, expressly outside this lease.

## 1. The missing parameter equation is now derived

Construction order matters. `try_new` counts Value components (`lib.rs:10092`),
sets `parameter_live_base` to their checked u32 count (`10142`), then allocates
one row in exactly the component's kind while appending matching level and
metadata (`10410–10449`). The later parameter loop (`10451–10465`) appends one
Value row, level and metadata per recipe position. Successful counter checks
precede publication. Thus after the loops, for every recipe p, q = base+p is
an allocated Value row. No row/level/metadata mismatch is introduced.

`initialize_candidate_source_levels` (`candidate_source.rs:2292–2328`) changes
levels without resizing. Its formal guard checks
`parameter_recipes.get(p) == Some(registration.parameter)` and no old native
root. Hence this particular p really is in the recipe vector, rather than an
arbitrary usize passed to the translator. Computation formals allocate their
separate entry Effect row with the checked fresh constructor after the root.

`shadow_apply.rs:4142–4157` supplies the previously missing definition:

```text
candidate_endpoint(Parameter(p), s)
  = live_value_term(s, checked_add(base, checked_u32(p)))
candidate_endpoint(Component(j), s)
  = live_value_term(s, live_components[j].ordinal).
```

`live_value_term` (`lib.rs:10595–10605`) calls `with_term_events` with precisely
`arena.live_variable(Value,s,q)`. On Ok, that wrapper returns the constructor's
term; capacity-event sampling can turn success into an error, never into a
different term (`10659–10685`). `live_variable` interns exactly that tagged node
(`term.rs:1205–1216`). The branch interner starts empty (`710`), reuses only a
previous equal-node handle, or appends the node and records that exact pair
(`1166–1203`). Append publishes the current branch brand and its initialized
page slot (`1083–1163`, `1550–1569`); lookup retrieves that slot by the same
brand/page/offset (`831–855`). This gives the displayed term-view equation,
including interner hits by induction over earlier successful interning.
No old node is overwritten and no row table is changed by this constructor.
`value_endpoint` then checks Value/sign and returns canonical ValueRow(q)
(`lib.rs:11839–11863`). Before graph installation canonicalization is identity;
after installation the equation uses the actual forest representative.

This proves D-PARAM at the exact `candidate_source.rs:2316` invocation. It is
not a theorem that arbitrary Parameter(p) inputs are validated: the translator
itself has no recipe range check. The formal guard and completed allocation
loops supply that premise here. This closes the specific R244 missing owner
premise without treating a live-variable tag as a row-allocation check.

## 2. Component and structural construction; retained input premises

For Component(j), the translator does **not** inspect the stored kind and uses
unchecked indexing. The valid equation is therefore:

```text
live_components.get(j) = Some(Value,q) AND allocated Value q
AND successful candidate_endpoint(Component(j),s) = t
  => term_view(t) = LiveVariable(Value,s,q)
     and value_endpoint(t,s) = canonical_value(ValueRow(q)).
```

The new owner supports the actual local producer of this premise:
`candidate_component` (`shadow_apply.rs:3873–3891`) calls occurrence construction
for Value and Effect in that order, then records `len-2` and `len-1`.
`occurrence_component` (`lib.rs:2075–2098`) appends the ComponentId, interns its
Component node, and appends the term/position association. On successful
collection, the initialization loop translates each of those positions using
its component's actual kind, so `positions.value` selects an allocated Value
row and `positions.effect` selects an allocated Effect row. A component Term
uses the frozen term-to-position table (`lib.rs:11830–11837`); a live-variable
Term carries its ordinal directly. These two paths are not conflated.

Source collection (`candidate_source.rs:1080–1142`) records parameter positions
at recipe append and stores exactly `positions[index].value` for ordinary Value
endpoints. The source walk's levels (`1221–1227`, `1280–1305`) use those stored
positions. Catch/Case binder endpoints either copy an already recorded Value
endpoint or use the binder Value position (`1412–1506`). These facts derive
allocation/kind for those local translations; they do not certify the entire
HIR ordinal/owner/source-plan correspondence or all later retention histories.

Current source admission uses these equations in `admit_candidate_fact`:
Group translates its child/result; Record translates every field, Tuple every
element and Variant every payload at Positive; their result is translated at
Negative (`shadow_apply.rs:4227–4257`). VariantCase and TuplePattern translate
specified binders at Negative and allocate a fresh Value row for every omitted
binder (`4259–4301`). Apply translates argument at Positive and result at
Negative, and obtains its Effect ports from the actual Effect position or a
fresh Effect row before constructing a Negative Function (`4303–4337`).
This is the concrete row/term-to-constraint path, not a test-generated state.
Other source/annotation/operation paths remain part of the unchanged domain.

The checked current arena constructors (`term.rs:1230–1404`, `1451–1492`) give:

| Constructor | Immediate successful construction fact |
| --- | --- |
| Function(s) | Visible Value/Effect/Effect/Value children at opposite(s), opposite(s), s, s |
| Tuple(s) | Nonempty ordered vector of visible Value children at s |
| Record(s) | Ordered fields with visible Value values at s; empty records allowed; field metadata copied |
| Variant(s) | Nonempty alternative family with visible Value payloads at s; zero-payload alternatives allowed; tags and payload order copied |

The input children exist before a new structural node is published. Thus a
finite acyclic child DAG stays acyclic; interning an existing equal node adds
no edge. Success checks immediate visibility/sign/kind, not live-row ordinal
range, source interpretation, label uniqueness or source soundness. No such
extra conclusion is imported.

FreshUse (`candidate_scheme.rs:4581–4603`) maps each captured canonical row once,
reuses an existing image, freshens qualifying local rows at the use level, and
otherwise shares the canonical source. Given allocated captured rows and a
valid kind-separated forest, every image is same-kind and allocated. Capture's
`row` checks its canonical key against level/metadata tables before appending
`Graph.rows` (`1990–2015`); `expand_node` stores the resulting graph-row index
(`2188–2195`). This proves validity **at that capture**, not for all future uses.
FreshUse reconstructs Node::Row from its image (`4761`), Function from four
completed children (`4765–4783`), and Variant/Record/Tuple from their stored
slices and completed children (`4784–4857`). Checked arena construction then
provides the table's immediate facts. The captured index, tail, view, context
and relation inputs still require retention from capture to reconstruction.

## 3. First remaining entry equation and both actual applications

The first equation this packet does not discharge is the following lifetime
obligation, **R245-RETAINED-REF-1**, rather than another missing native translator:

```text
For each real production checkpoint cp followed by a rollback after which
production actually continues, and each surviving captured/FreshUse reference r
later read by prepare_candidate_fresh_use/freshen_candidate_graph_core:
  if r is a captured RowKey k, rep_after(k) is allocated in kind(k);
  if r is a structural Term t, lookup_after(t) has the required same tag/ports;
  if r is an EffectOperand/context-view (view,member,tail,weight), its view,
     member, tail and payload certificate remain valid together;
  if r is a bound relation/context/source/scoped ID or a restoration/replay
     owner/head, the retained ID/head still designates its actual old inventory.
Equivalently: every surviving such reference was valid in cp's retained prefix,
or its owning post-cp record is removed/restored before it can be read again.
```

Exact producer/retainer owners: `Capture::row`/`expand_node`, capture publication,
`prepare_candidate_fresh_use` and LocalUse/FreshRoute retention in
`candidate_scheme.rs`; restoration/replay/bound fibers in `candidate_context.rs`.
Exact destructive/restoring owners: `rollback_route_transaction`
(`lib.rs:9711–9863`), branch term rollback (`term.rs:803–829`), intrusion rollback
(`candidate_intrusion.rs:195–223`), algebra rollback (`candidate_effect.rs:689–738`)
and context rollback (`candidate_context.rs:2182–2280`). Consumers include the
unchecked captured-row indexing at `candidate_scheme.rs:4583–4584`,
`rows[row]` at `4761`, view operands at `4660–4687`, and relation-context lookup
at `4699–4701`. All these defining owners are inside the admitted pins. No
missing external file or source dependency is fabricated.

The following narrower facts are derived and do not establish the quantified
survivor equation:

- `begin_route_transaction` saves row lengths, route lengths, source frame and
  the old LocalUse cursor (`lib.rs:9486–9508`). Row rollback restores journaled
  old rows then truncates new rows/levels/metadata together. Term rollback
  removes new interned entries/pages/backings and truncates the old last page.
- New LocalUse graph and FreshUse are built atomically before its frame is
  pushed (`candidate_scheme.rs:5281–5308`). A failed initial transaction had no
  saved cursor and clears `local_use`; a preexisting frame restores its cursor
  (`lib.rs:9747–9750`). `step_candidate_local_use` ownership is restored before
  its fallible result propagates (`candidate_scheme.rs:5318–5325`). This avoids
  misclassifying that local push/pop mechanism as a demonstrated dangling frame.
- Context rollback restores old typed frames, restoration/replay cursors and
  replay-head map entries, removes new operations, then truncates relation,
  source, context and fiber suffixes. Algebra rollback restores capture links
  and buckets before truncating records/views. These are actual inverse writes;
  their presence does not enumerate every survivor or prove that every prior
  mutation used the right journal before publication.

No counterexample to the lifetime equation is established. Its truth has not
been refuted; its exhaustive production preservation proof has not been
completed. Entry construction stops at this exact unresolved equation. This
is not a demand for full restoration after every error: the quantifier includes
only states actually reused for later production, as required by the approved
abnormal-path rule. A discarded private attempt need not be restored.

Other R70 W groups have the following exact status:

| W group | Derived local facts | Remaining premises at a later call |
| --- | --- | --- |
| Rows, levels, metadata, forests, bound lanes | Initial/fresh alignment; D-PARAM; produced Value-position equation; singleton forest extension, distinct-root link and compression; bound owner range/kind and physical lane readback | Allocated references at every later emission/transport; R245-RETAINED-REF-1; item sign/row/term validity is not checked by lane selection |
| Visible finite structural terms | Current checked four-port and three vector/family constructors; successful native equations above | All accepted producer indices and retained child/component interpretations; no stale truncated suffix |
| Views, members, payloads, capture incidence | Signature view appends its actual ID; view copy preserves allowed list/provenance after payload validation; append/splice preserves finite chains given valid disjoint inputs | Tail allocation and source payload/member inputs; continued-history ownership equation; no invented member-to-origin association |
| Evidence, contexts, fibers, replays, queue ownership | Exact-key fibers link to older entries; replay construction retains actual ordered dependency parents; checked cursor transfer; local rollback inverse writes | Valid source/context/scoped/relation inputs and survivor/head/owner history; raw-slot canonical coverage is separately R71 |

In detail, `candidate_insert_bound_with_evidence` (`candidate_extrusion.rs:702–876`)
canonicalizes owner/item, checks owner range and matching kind, chooses the lane,
appends, and reads that actual slot back. It does not validate the item's row
range or structural sign. Merge (`candidate_intrusion.rs:599–733`) copies both
sides while raw storage remains, transports evidence, then links distinct roots.
Under allocated same-kind inputs the forest stays finite and kind-separated.
`attach` (`candidate_context.rs:3702–3716`) appends a decreasing next-index chain;
source/context/RelationId validity remains an input. No all-history conjunction
is silently inferred from these constructor-local implications.

At the two actual calls:

```text
call+  lib.rs:14822: extrude(Value(lower), Positive, value_levels[upper_row])
call-  lib.rs:14835: extrude(Value(upper), Negative, value_levels[lower_row])
```

Graph presence, nonrow Value root and the displayed sign/target come from the
branches. The canonical-task guard (`14571–14578`) returns/requeues before either
call. The typed frame retains the same item through Transport, Context and
Dispatch (`14399–14465`); its actual pair and relation, rather than an endpoint
label guess, supply the processing projections used by extrusion Parents.

D-PARAM and the produced-Component equation apply to their source row roots in
**both** histories. Successful fresh allocation and valid canonical transport
then preserve their row-kind/level-table interpretation. The structural table
applies to either root sign and every traversed structural child; FreshUse
applies with the captured inputs and retention premise above. At call+ the target
is the actual upper row's level; at call- it is the actual lower row's level.
For each, the allocation premise must reach that particular row through its
history; the unchecked level read is not a validation. Views and fibers use the
same actual inventories at either call and retain their listed premises.
Thus C-ENTRY remains conditional separately at each call. D-PARAM removes one
base premise from each derivation; it does not justify either complete W.

## 4. Independent current entry-to-return simulation

This section reads current `candidate_extrusion.rs` directly. It does not apply
the historical Function-only theorem to new cases. A completed successful
return from either actual call has a Value root image: rows map Value rows to
Value rows; Value structural/atomic cases map to Value, and the final lookup
uses that root key (`candidate_extrusion.rs:80–95`, `575–588`). This narrow
postcondition is not a success, termination or semantic-soundness guarantee.
The caller envelope alone does not establish safe traversal of all referenced
rows, DAGs, views or fiber heads. The stronger C-RETURN uses WCurrent explicitly.

Use actual key `(canonical endpoint, polarity, target)` and local maps R/S,
stacks K/P (structural work / pending bounds), view map V, append-only port
array U and initialized allowances I. An adequate current invariant is:

1. Representatives and old row levels do not change inside the call. Fresh rows
   have target level. Local helpers append storage/metadata; no typed child
   dispatch or intrusion settlement runs here. R/S have disjoint row/nonrow
   domains, with one completed same-kind image per key.
2. A low row maps to itself without bound traversal. A first deep row snapshots
   selected direct/exact lengths, allocates a same-kind level-target copy,
   retains its Parent and inserts R **before** adding the opposite-side source
   link or scheduling descendants (`95–195`). Repeated keys reuse the image;
   opposite signs remain distinct keys. Every selected physical slot keeps its
   exact original BoundKey; canonicalizing its child does not rewrite that key.
3. K is popped before P. A structural continuation is below its children in K.
   A row-bound Visit/Bound goes into P, preventing a bound back-edge from
   reopening a structural node currently being reconstructed. U records each
   vector/family's child keys and original terms in its own immutable interval;
   nested appends/reallocations preserve earlier indices and entries.
4. Each discovered dependency has its actual pending continuation, and every
   continuation's child images are completed before it executes. R cuts row
   cycles; finite structural DAGs and finite view-tail/capture chains from W
   justify the rest. Bounds/views/fibers are taken from the mutable visit-time
   state, never substituted by an immutable entry snapshot.
5. Copied bounds, exact observed source fibers, Parents, groups and replay
   operations have their actual separate owners. A transport gap is recorded
   as a gap; it is not filled by guessing a relation from origin metadata.
   The outer queue can already contain work, and local replay transfers no
   acknowledgement. All checked allocations/helpers must succeed for the
   successful claim; an error is propagated, not a successful partial result.

The cases below preserve this invariant, conditional on its explicit inputs:

| Current Work case | Construction and continuation correspondence |
| --- | --- |
| Visit(row) | Anchor or early-memoized fresh same-kind row; snapshot before its own opposite-side link; exact physical slot Visit/Bound pairs; positive Effect row also schedules actual incoming capture incidence records |
| Visit(atom) | Identity in S; no reification required |
| Visit/EffectView | Tail Visit at the same sign; continuation requires its row image, remaps by `(old view, mapped tail)`, preserves Support/Allowance/AnnotationMember tag and member ordinal |
| Visit/Function | Four children in Value/Effect/Effect/Value at opposite(p), opposite(p), p, p; reverse push yields source-order DFS; changed ports reify at their own signs; constructor validates all four; unchanged node reuses original |
| Visit/Tuple | Term tag/sign and stored arity are checked, arity nonzero; append one `(child key, original term)` per element at p; checked interval and completed children drive ordered reconstruction at p, keeping arity |
| Visit/Record | Term tag/sign checked; append fields' Value child keys at p in field order; continuation clones actual fields and changes only values; names and presence metadata survive; empty record reuses original |
| Visit/Variant | Term tag/sign checked; checked sum of payload counts gives flat interval; alternatives and payloads flatten in their physical order at p; continuation clones alternatives, consumes exactly that interval and changes only payload terms; tags, alternative order and payload arities survive; zero-payload alternatives need no child work |
| Bound | Completed child image installed on selected copied side; transport uses the original physical BoundKey, preserving its actual fibers separately from bootstrap evidence |
| IncomingAllowance | Source Visit finishes before cut installation; negative copied view uses mapped tail; source fiber transport succeeds before the installed cut enters I |

Current owners: discovery `candidate_extrusion.rs:196–333`, EffectView/cuts/bounds
`334–417`, Variant `418–467`, Record `468–504`, Tuple `505–541`, Function
`542–574`. For Record, zip length equals the original field count because that
same immutable view supplied both len and U's interval. Variant explicitly
rejects either missing or surplus flattened children. Tuple checks completion
before comparing images. Record/Variant's `any` could observe an absent map as
changed, but invariant 4 proves presence on an admissible path; on a changed
path reconstruction also checks every child. Empty Record / zero-total-payload
Variant have no changed child and retain the original. No tuple of zero arity
is smuggled in as such a case.

`candidate_endpoint_term` (`594–616`) reifies rows and current structural tags,
including all three new forms; it is intentionally partial on atoms/views.
Every changed Value child image is a row or reconstructed Value structure.
An atom is unchanged and keeps its original term. Function Effect children
originate as effect terms (rows or effect leaves); unchanged leaves keep their
original terms. Thus no changed atom/view is passed to this partial helper.
Views are reconstructed by their separate EffectView continuation. Success of
the arena constructor then rechecks the required kind/sign and branch visibility.

Mutation/termination argument: each original high row expands at most once per
sign, generating at most two same-kind copies, both at target level. Generated
rows are anchors. Bound writes target copies; incoming cuts target a mapped
positive source, an anchor or copy. Original high rows acquire only their
opposite-side source links, so a later opposite-sign snapshot can include that
real synthetic bound. Copied/incoming views have tails at target-or-lower level;
no new high-tail incidence record is appended to a bucket during its positive
Visit. W supplies the finite preexisting buckets, term DAG and fibers. The
three additional structural forms add only their finite actual child counts;
U keeps stable intervals and finite sums. Hence the discovery envelope remains
finite. This is local termination with successful helpers under W, not global
solver termination or a constant/linear runtime bound.

When K and P empty, the root image is present. Every visited deep key has one
same-kind level-L copy and Parent, its actual opposite source link and selected
visit-time bound copies. Every reconstructed port/vector/family obeys the
case table. Sharing is by full key, not by nominally distinct term IDs: interning
may return equal nodes. No semantic solution equivalence follows just from
these structural properties.

## 5. Return retention, replay and separate later owners

`finish_candidate_extrusion` (`candidate_intrusion.rs:368–387`) runs before final
replay. With no new Parents it adds no group. Otherwise the active processing
pair on this route yields the actual by-output index and exact appended Parent
interval/occurrence. Qualification reads the retained source events; this local
recording does not prove source SCC/intrusion adequacy.

Only IncomingAllowance adds the opposite side of a copy initialized with
selected lowers. It records the installed cut in I only after transport.
The final I pass (`candidate_extrusion.rs:583–590`) therefore occurs after all
selected bounds and fibers finish. `candidate_replay_bound:1070–1113` enumerates
the actual opposite count and constructs ordered physical lower/upper BoundKeys.
This does not claim that every raw storage slot has every canonical fiber;
**R71 raw-slot/canonical-fiber coverage remains separate**. In particular Bound's
raw source and canonical child/destination are kept distinct throughout this note.

`candidate_transfer_bound_origins` (`candidate_effect.rs:1045–1096`) first walks
actual fibers from the exact source key and transports each executable witness.
Its later origin-table pass lacks an origin-to-fiber association, imports
metadata with explicit MissingOriginAssociation and relation None. Neither pass
identifies origin count with fiber count or invents a common witness.

Current replay construction (`candidate_context.rs:4411–4499`) snapshots actual
fiber heads and old replay heads, enumerates new-lower × all-upper then old-lower
× new-upper, retains exact ordered input/dependency parents, unions their
sources and composes scoped payloads. Equal resulting RelationIds do not erase
distinct dependency parents. Repeated exact dependencies can suppress children.
The old-head suffix invariant is an explicit W premise; merely storing head
numbers does not prove it. Scoped rejection/error is propagated.

Each new operation retains children with q=c=0. The final pass uses
`candidate_context_drive_replay(id,None)` (`4625–4648`), whose None consumer
(`4598–4619`) only queues children. `enqueue_item` reserves evidence/queue/undo
before exact cursor transfer and then pushes infallibly (`lib.rs:15328–15355`).
Thus at every frontier `0 <= c <= q <= n`, transferred children remain owned by
queue/current/drain records, and the untransferred suffix stays in the retained
operation. For a successful full nonempty local drive q=n and c=0; an empty
operation can retire. A strict prefix q<n describes an intermediate/error
frontier, not a successful early exhaustion of this drive. This pass performs
no typed drain, acknowledgement or settlement.

Only after final replay and the resource sample succeed does the call return;
local maps/stacks/U drop and their scratch charge is removed (`590–593`).
Parents, views, fibers, groups and queued/retained replay ownership remain.
The caller can enqueue its rewritten Value afterward (`lib.rs:14846` onward);
this is not a descendant-completion barrier.

Actual later owners are `step_typed_drain` (`lib.rs:14394` onward), terminal
acknowledgement via `candidate_step_typed_drain_terminal`, and
`complete_replay_child` (`candidate_context.rs:2596`). They process the saved
frame, diagnostics, possible intrusion settlement and exact replay child index.
**R70-DRAIN-1 remains OPEN**: q=n, a returned image, or one local frame action
proves neither eventual later execution/settlement nor independent foreign
continuations. No publication/soundness claim is added.

## 6. Reuse, review boundary, TODO and stop receipt

Reused: R244's reviewed allocation/constructor inventory with its actual
predecessors; R70's visit-time snapshot insight and queue-versus-completion
distinction. Historical R70 froze Function-era source hashes, including
extrusion `fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d`,
term `f3a0c3875ba1ba8c80ee48a405faf3dad22b57cba8930394f99181201bc58f60` and
lib `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee`.
Current claims use current pins. No historical source bytes were used as
current implementation evidence. R70 review does not review this packet or the
new structural cases. Rejected: W assumed as constructor proof, ordinal range
inferred from a tag check, unchanged entry snapshots, historical case extension
by name, origin/fiber collapse, transfer as completion and a rollback function
as a complete survivor proof.

TODO `R245-RETAINED-REF-1` to Luna: keep the same parent and inputs; prove the
specific survivor/journal domination equation in §3 over actual continued
production histories, starting at the listed FreshUse consumers and enumerating
which retained captures/rows/operands/contexts survive each owning transaction.
The local LocalUse mechanism already analyzed above should be reused, not
replaced by a test-only pause argument. Required falsifier: an accepted source
prefix actually retains a removed/wrong-kind/tag-invalid reference and reaches
one of the two real calls. A hand-built graph or test-only route is insufficient.
No such prefix was produced. If a new owner/dependency or implementation lease
is needed, return that precise change to Luna before using it.

This packet changes method from the prior missing-translator search to direct
native construction and current case accounting, but does not rename the
remaining all-path premise as a closed result. The next step is the exact
remaining lifetime/source inventory edge, not another conditional restatement.
R71 and R70-DRAIN-1 are independent TODOs with their existing owners.
Implementation disposition **NO_SAFE_CODE_SLICE**: actual bound emission and
actual replay owners were inspected; no reachable defect justifies a repair.

Checks: read-only source/symbol searches and SHA-256 comparisons; all 17 R244
manifest pins plus the extra shadow_apply pin and both contracts matched before
source claims. R244 artifact hashes and admissions are separately recorded
below. One malformed rg expression failed without reading/mutating source and
was corrected; no failure is concealed as verification. No Lean, Rust build,
Cargo, tests, probes, benchmarks, Git, external contact, runtime/quarantined
paths, scratch/cache writes or descendants. New paths are exactly this note
and the assigned R245 inbox; scratch NONE. No independent certification by its
producer; fresh compiler_referee review/intake/integration belong to Luna.

Requested model/effort: gpt-6.1-sol/high. Observed model/effort: UNKNOWN.
Current worker `/root/sol_r245_entry_return`, session
`01a1873a-a93b-7dc3-a8ce-028a7b543a80`; parent assignment and active hash-gate
collaboration receipt supply launch/work evidence. Contract budgets: entry
<=1800 active seconds, return <=1200, no descendants. Exact active time, CPU and
RSS UNKNOWN; full reservations remain charged, no return of unobserved time.
A clock observation during work was 2026-11-02 03:18:13 UTC; it is not a complete
active-time measurement. No renewal or model-switch claim.

Writer state after final hashing: **STOPPED / WRITES_STOPPED**. Both outputs
freeze at handoff revision 1. No descendants/unresolved descendant leases.
Independent review and any integration remain pending; parent stays OPEN.

## Frozen dependencies

The R244 manifest and extra source pin were recomputed, all MATCH:

```text
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7  notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md
4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf  tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md
25f6a370ae1aa2d7a623a8aa0eaede979248d85b8c03c894fbf8f7850775e8db  tasks/agent-loop/inbox/20261019-r70-proof.md
ff2c149bd71c783f874c150404bf199084858df631c21899d3abf53a258655bb  tasks/agent-loop/inbox/20261019-r70-closeout.md
a93b2e5d38c03511c768dd704e57f3b616a1dafc591fe62a4155d64a06bbf4d8  notes/progress/2026-10-19-r70-closeout.md
429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be  crates/yu-solver/src/lib.rs
d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1  crates/yu-solver/src/term.rs
80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61  crates/yu-solver/src/candidate_extrusion.rs
bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49  crates/yu-solver/src/candidate_source.rs
6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e  crates/yu-solver/src/candidate_scheme.rs
4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15  crates/yu-solver/src/candidate_effect.rs
475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97  crates/yu-solver/src/candidate_intrusion.rs
a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905  crates/yu-solver/src/candidate_context.rs
4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03  crates/yu-solver/src/candidate_scope.rs
aaaa88a374083f898188cd390b8cf0244855d8c09c8939b9e68ee2831bc692cf  crates/yu-solver/src/candidate_value_graph.rs
5ca308e7b890e57a8458a151554ece55585d762565204d39c520c4b534e44ade  crates/yu-solver/src/candidate_receiver.rs
99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5  crates/yu-solver/src/shadow_apply.rs
d79236d7b5e13b739c24e45b728f7b55db19eceebc5effce83e61b8e81555e61  tasks/agent-loop/sprints/ordinary-extrusion-native-entry-r245.md
07815becba7a8f9e0584bdb289a49f3f81907c7b1d3394eb3dc35fca3aa6f3ec  tasks/agent-loop/sprints/ordinary-extrusion-entry-construction-r244.md
396323d6eb3cee6d856e8c0e1bb7c86648405bcce296219f62511431631c4fcd  notes/theory/2026-11-02-ordinary-extrusion-entry-construction-r244.md
1c0f5131c81ca45b4f0f12751e5a8020b5945716b2615317b9aff66e4c1018af  tasks/agent-loop/inbox/ordinary-extrusion-entry-construction-r244.md
2535bd5cab2c2397192478925601719ee2fc23474fe45bc8768defb81860e0b7  tasks/agent-loop/history/20261102-r244-admission.md
77bd3c3ea324caf3c6d4b876ce204f83e6086363e09bfe51b49a76b99a4d8fb4  tasks/agent-loop/history/20261102-r245-admission.md
```

Historical R70 sources are provenance only, not current pins. R244 authorship
is `/root/sol_r244_entry_wf`; R70 authorship/contribution remains as recorded in
its pinned note. Their authors do not independently certify this R245 result.
The theory output hash is in the handoff; the handoff hash is supplied externally
to avoid recursive self-hashing.

# R247: successful-history row and term reference closure

Status: **candidate source-native derivation, awaiting independent review**.
Revision 1. Author `/root/sol_r247_successful_history`; no coauthors or
descendants. Contract `successful-row-term-closure-r247`, final SHA-256
`39cd761d094e5a22524ed0b03f75b2efd9a8d86921027cb9765459ee1029ac1d`.
Baseline `da4bcaeeacd369e218e7a9d3b6d85acc6fe72f52` was observed by reading
`.git/HEAD` and its named ref, without a Git command. All 18 final manifest
dependencies matched their admitted hashes before use; see the appendix.

## Claim, quantifiers and application boundary

The unchanged parent is Yulang inference soundness and its Rust implementation,
at `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1` / `R70-ENTRY-WF-1`. The accepted
source domain, Simple-sub A/B, arbitrary independent satisfying assignment,
shared witnesses, F1/FK1 and semantic choices remain unchanged. These inputs
contain no fully quantified concrete full-inference Lean theorem; this packet
does not invent one. No Lean declaration, theorem type or axiom dependency is
claimed; the checker is NOT RUN under the source-only lease.

The result is a storage/reference argument at the actual native call sites,
not semantic solution equivalence. Write `V(S) = [0, bounds.len())` and
`E(S) = [0, effect_bounds.len())`. A row's kind is its typed region, not its
numeric ordinal: Value(3) and Effect(3) are different references.

The derived invariant `HRT` has the following clauses on references reachable
from the production constructors, retained graphs, bound tables and typed
work items used below:

1. Value/Effect row references belong to V/E, respectively; their levels and
   metadata have matching allocated entries.
2. A referenced term is visible in this session's actual arena. Its node is
   the claimed leaf/live/structural variant. A live child has the claimed kind
   and sign and names an allocated row of that kind. Function children have
   kinds V,E,E,V and signs opposite,opposite,same,same. Tuple/Record/Variant
   value children have the parent's sign.
3. A collected Component term has its exact frozen recipe association. The
   associated raw row and its current representative are allocated in the
   component's kind. Native Component translation and translation of that
   collected term use the same raw row and therefore the same representative.
   An ascription facade's alias is a separate source-planning association.
4. Stored direct bounds and structural endpoint handles retain these row/term
   facts. A view's optional tail, when used to generate a row child, is an
   allocated Effect row. This last row fact does not certify the view's member,
   payload, authority or context interpretation.

Informal result type (static source derivation, not kernel-checked):

```text
D-RT:
For every accepted non-test production construction and every execution prefix
that reaches lib.rs:14822 or :14835 in its private session,
HRT holds on that call's receiving row and root and on every row/term reference
used by the emitted Work::Visit/Function/Tuple/Record/Variant/Bound children.
It continues to hold at successful native allocation, reconstruction, bound
emission, canonicalization and retention steps inside that invocation.

C-ENTRY-REMAINDER:
D-RT + the remaining view/member/payload/evidence/context/incidence/ownership
clauses of WCurrent => WCurrent at either actual call.
Those remaining clauses are not assumptions used to prove D-RT's row regions.
They remain needed for complete entry admissibility and R245's return theorem.
```

Here a prefix may retain ordinary type diagnostics and may precede a later
failure. It need not be a completely successful solve. Earlier returned
availability failures followed by inference in the same production session
are excluded by the reviewed R246-EXIT result, as admitted by this contract.
R246 does not supply HRT: the successful-step derivation follows below. Private
test calls that manufacture graphs/ordinals and post-error retry scripts are
outside this actual call graph, not excluded source-language forms.

**Parent application: REDUCED.** D-RT removes the row/term conjuncts of the two
R245 entry applications. Full WCurrent, the return theorem's other premises,
whole inference soundness and production promotion remain OPEN. This is a
producer's candidate derivation; Luna's fresh review decides acceptance.

## 1. Source allocation precedes endpoint planning

The extra HIR owners were admitted by Luna before their contents were cited.
Their role here is only the occurrence/member/index bridge.

`LocalSourceIndex` and `LocalSource` have private owner/index/vector fields
(`yu-hir/module/local_source.rs:50–77`). The index constructor is
`Builder::slot:1484`: checked current vector length, append a slot, return that
same owner's index. The root, named Lambda bodies, defaults, generated strings
and structural children retain these allocated indexes; the builder publishes
the vector only after every slot contains an expression (`1334–1356`).
`set_at_range:1520` fills an allocated slot; generated-string construction first
allocates a slot (`1552`). Public access is immutable, and `expression:174`
checks both owner and index. Thus this bridge comes from actual source
construction, not from assuming successful solver indexing validates an ID.

For ordinary carriers, `order_occurrences:131–163` first records each expression
index once in its source-key bucket. Removing a bucket when its syntax node is
visited prevents a second visit from assigning those indexes again; a leftover
bucket rejects publication. Each index gets a checked shared `next_occurrence`,
except the body of an Expression owner, which reuses that owner's authenticated
ordinary root. `form_ordinary_with_root_parameters:1025–1081` commits the staged
counter only after successful formation/order/merge. The allocator
`module.rs:2751–2760` increments with checked addition. Occurrence equality
includes the exact artifact pointer and ordinal (`1438–1451`); equal numeric
ordinals in different HIRs are not equal occurrences. Compatibility local
carriers use the same checked allocator through `set_at_range`. The ordinary
fallback uses fresh child occurrences in `finalize_ordinary_admissions:2980`
and distinct Lambda/body occurrences in `module.rs:3625–3690`; no simultaneous
parent/child reuse is introduced by the root-replacement operation.

Collection rejects duplicate direct expression occurrences and definition
roots (`solver/lib.rs:1211`, `1875–1895`). `emit_candidate_source:1037–1069`
requires its source to be the exact object returned by `hir.local_source_for`
and checks source-owner/HIR ownership before creating expression components.
This also handles a possible duplicate member-owner inventory without assuming
that a HashMap insertion checks uniqueness: HIR's carrier index maps select
one retained element (`module.rs:2702–2712`); `local_source_for:2022` returns
that element. The member loop (`solver/lib.rs:1372–1387`) visits each Supported
element. An earlier duplicate Supported element cannot pass pointer equality
with the selected later element, so no successful batch can emit both. Repeating
the same HIR in a world similarly encounters direct-root rejection or the
different `hir_index` check in source emission. Different owners' overlapping
occurrences are rejected by `source_owners`. No uniqueness conclusion is taken
from `owns_occurrence`, whose implementation checks artifact branding only.

For each expression, the first planning pass calls `candidate_component`
(`candidate_source.rs:1099`; `shadow_apply.rs:3873–3890`), appending Value then
Effect. `occurrence_component` and `definition_value_component`
(`lib.rs:2075–2114`) append corresponding component IDs and prefix terms at
matching positions. The successful unique-occurrence/root path just derived
makes `component_term_positions[component_terms[j]] = j`; the debug assertion
on insertion is not the proof of that equation.

Root parameters, Lambda parameters and record binders get recipe positions
from the old length before append (`candidate_source.rs:1082–1124`). Initial
expression endpoints select either this parameter map or `positions[i].value`
(`1140–1150`). Catch/Case binders copy an existing endpoint or a previously
allocated Value position (`1380–1510`). Ascription copies `positions[child]`
and `endpoints[child]` (`1152–1161`, `1934`); it changes the facade's occurrence
lookup, not `component_term_positions` or the old Component term's identity.
Block recursion links, Group/Sequence/If/Case/Catch result links, Tuple/Record/
Variant ports, Apply registration and field-tail obligations are built from
these typed endpoint/position vectors. No branch uses an Effect position as
a CandidateEndpoint Value. The legacy candidate expression constructor
(`shadow_apply.rs:3974–4140`) has the same result type: Value endpoint plus
Effect position; its Parameter case selects an appended formal recipe.

This proves the required planning equation:

```text
every emitted CandidateEndpoint::Parameter(p): p < parameter_recipes.len()
every emitted CandidateEndpoint::Component(j): j < components.len(), kind(j)=V
every emitted computation-effect position k: k < components.len(), kind(k)=E
```

It does not assert that arbitrary calls to the translator validate these facts.

## 2. Typed rows and exact native translations

`try_new:10092` counts Value/Effect components, sets `parameter_live_base` to
the checked Value count, then appends one row of the component's kind and
matching level/metadata per frozen component (`10410–10449`). Parameters append
Value rows afterward (`10451–10465`). Induction over these loops gives:

```text
live_components[j] = (kind(components[j]), ordinal of that kind's birth)
Parameter(p) raw row = parameter_live_base + p < bounds.len()
```

Initialization of source levels does not resize the tables
(`candidate_source.rs:2292–2302`). Formal registration validates its exact
parameter recipe before native translation; a computation formal's entry row
is separately allocated with `fresh_effect_at_level` (`2303–2327`). There is
no requirement that the forest already cover all these rows.

`fresh_value_at_level:10521–10545` and `fresh_effect_at_level:10552–10582`
compute the checked old length, reserve before appending, and append row,
level, metadata and traversal mark in their own kind. On return, the ordinal
is in the newly extended typed region and all old row references remain valid.
Levels and non-generic flags may change later; typed-region membership does
not depend on their values.

The actual native equation is `shadow_apply.rs:4142–4157`:

```text
candidate_endpoint(Parameter(p), s) = live(Value, s, checked(base+p))
candidate_endpoint(Component(j), s) = live(Value, s, live_components[j].ordinal)
```

The translator does not check Component kind or parameter range. Section 1
and completed allocation supply both at its actual callers. For the collected
term t = component_terms[j], `component_endpoint:11830` uses the frozen term
map, so its raw ordinal is exactly the same `live_components[j].ordinal`.
`value_endpoint:11839–11863` canonicalizes that row in both the Component and
LiveVariable cases. Section 5 proves this yields the same valid current Value
representative. The Effect version uses its own typed region (`11900–11919`,
`13577`). This strengthens the R245 Parameter-only equation to both native
forms at their real producer positions, without making unchecked inputs valid.

## 3. Term visibility, tag, sign and child rows

Prefix construction interns only actual Component/Leaf nodes at these
collection sites (`lib.rs:2086`, `2106`, `2163`). `TermBuilder::intern/seal`
(`term.rs:344–398`) records exact nodes with the collection brand, seals before
batch observation (`lib.rs:1477–1485`) and retains the immutable prefix.
`ConstraintStore::with_hirs_and_capacity:3496–3513` uses that exact batch
lineage to start the branch, including every imported HIR collected in this
world. Imported source does not contribute sibling-branch term handles.

For the branch, maintain `positions[node] = t => lookup(t) = node`.
The directory starts empty (`term.rs:707`). On a miss, `intern:1166` reserves,
appends `node.clone()` and records that exact pair; a hit is full node equality,
not hash equality or nominal freshness. `push:1083–1163`, checked shared page
claims (`1405–1423`), initialized page slots (`1550–1571`) and lookup
(`831–855`) compose into exact visibility. New pages use aligned post-prefix
bases; old initialized slots are not overwritten by successful extension.
Begin/commit (`746–801`) preserve these nodes/directories. Rollback can truncate
and reuse a last-page offset; unrestricted rollback persistence is deliberately
not asserted. R246 excludes its later production inference continuation here.

`live_variable:1205–1216` copies kind/sign/ordinal exactly. It checks **no row
range**. Its ordinal proof is section 2 or the captured/fresh row proof below.
The wrappers `lib.rs:10595–10685` return that same constructor term on Ok;
accounting can turn success into error, not change its payload.

Structural constructors validate visible immediate children and kind/sign
before publication (`term.rs:1230–1403`, `matches_endpoint:1451`). The live
child ordinal is still justified by its birth, not those checks. Positive
Function children are V-,E-,E+,V+; Negative reverses them. Tuple is nonempty,
Record may be empty, Variant has a nonempty family with possibly zero payloads.
Their children keep order, field optionality/names or alternative tags/payload
intervals. Interner hits retain the same payload equation. Because each new
structure names already visible terms, structural descent is a finite DAG;
cycles in the solver pass through row bounds, not cyclic structural terms.

Actual row-supplying constructor families are covered as follows:

| Production construction | Row witnesses preceding live/structural terms |
| --- | --- |
| Source Group, Tuple, Record, Variant, TuplePattern, VariantCase, Apply (`shadow_apply.rs:4227–4378`) | Section 1's endpoint positions; pattern wildcards call fresh Value; Apply return effect calls fresh Effect; structural constructors receive exactly these terms |
| Lambda (`lib.rs:11620–11828`) | Appended formal, typed body positions; registered computation entry from initialization or fresh Effect; fresh returned Effect; stored domains came from the checked negative term constructors |
| Annotation variables/holes/formal ports (`candidate_effect.rs:1675–1748`, `1804–1976`, `2066–2103`, `2540–2824`) | Caches start empty and insert only fresh Value/Effect rows; hits retain those rows along successful history; record defaults use fresh Value or appended parameter rows |
| Operation, primitive, Catch continuation and operation-v1 (`candidate_effect.rs:1280–1520`, `2540–2824`) | Signature environments insert only fresh rows; original/payload/continuation/effect positions come from source planning; entry/return ports are fresh Effect; the `__operation_v1_q` lookup retrieves its signature-created Effect row |
| Operator use and selected member (`candidate_scheme.rs:3500–3605`, `3960–4020`) | Typed source positions or fresh Value/Effect; selected member interface uses exact indexes of the captured graph and this same FreshUse row map |
| Local exposure (`candidate_effect.rs:2240–2290`) | Annotation structures above plus fresh Value root, retained before PublishLocal |

None of these cases identifies original raw rows with their equalized
representatives or identifies two distinct FreshUse instances. The exact raw
association is retained while current endpoint readback canonicalizes it.

## 4. Capture and FreshUse close the successful retained-input edge

Capture's row constructor (`candidate_scheme.rs:1988–2046`) canonicalizes a
typed RowKey and obtains its level and metadata with checked `get` before
appending `Row { key, local }`. Matching row/level/metadata lengths from section
2 make that an allocated typed row. This is an actual ordinal check, unlike
`live_variable`. Its returned graph-row index is the just-appended position;
a hit reuses that same checked row entry.

`intern:1909–1955` allocates a graph node and pending entry before returning
its index. `expand_node:2181–2340` stores Row indexes only from `row`, and all
structural child indexes only from `intern_shape(term_endpoint(...))`. The
latter reads the actual term and validates kind/sign/tag (`2048–2180`).
Flattened Tuple/Record/Variant ports store these returned indexes; no index is
manufactured from an ordinal of another inventory. The capture loop drains
new pending nodes and rows before returning (`2928–2980`). Placeholder nodes
are private construction state, not a second import format. A successful
published Graph therefore has actual allocated Row keys and valid term-node
indexes. Its structural shape is copied from the immutable term DAG.

Contexts can discover an additional negative demand root or view-tail node
(`2960–2979`); the same term/row constructors check those added graph nodes.
This fact does not establish the source authority of that context or payload.
Extra member receiver/body-effect roots are explicitly seeded and checked
(`2915–2927`, `3310–3352`), not assumed reachable from the result.

The source session retains these graphs in module/operator/member/local
owners. Successful histories never truncate their row regions or arena nodes;
dropping a temporary graph/map does not drop the rows/terms it designates.
The actual destructive row/term operations are rollback
(`lib.rs:9851–9859`, `term.rs:803–829`); R246 excludes their use as the prefix
of a later production extrusion. A future failure does not invalidate an
earlier prefix. Thus captured references retain their row/term meaning through
all successful extensions, even if their representative changes.

`prepare_candidate_fresh_use:4527–4598` canonicalizes each captured row. If
it reuses an image, that image came from the same map's preceding valid row.
Otherwise it chooses either that valid source representative or a fresh row
of the same kind. This proves every `rows[i]` has the captured row's kind and
belongs to its allocated region, in the actual iteration order. It specifically
justifies the unchecked indexing at `4583–4584` and `4761` identified in R245.
There is no remaining row-lifetime hypothesis at those equations on this
successful production branch.

Reconstruction (`4744–4855`) uses visible collected leaves, live terms of
those mapped rows, and checked structural constructors with actual child
terms. Captured tail references use graph Row nodes and reject a non-Effect
image (`4660–4687`, `4710–4715`). A renamed scoped demand root is retrieved
from the same rebuilt term map (`4878–4879`). `begin_candidate_fresh_bound`
(`4950–4994`) reads the captured kind/orientation and those reconstructed
terms/operands, yielding the proper lower-positive/upper-negative endpoints.
It then passes them to the actual physical restoration owner. Evidence import
(`4918–4948`) does not manufacture row/term values or convert evidence identity
into an allocation witness.

Module/import, local, operator and member uses all use this Capture/FreshUse
path (`candidate_scheme.rs:3192–3352`, `3460–3605`, `3950–4020`, `4995–5078`,
`5281–5325`). LocalUse retains graph and FreshUse before the frame is pushed;
pop/step/push restores ownership before propagating the result. Existing
successful captures and copied uses remain separate instances. Legacy closed
instantiation, if considered separately, also allocates each substitution row
before storing it (`lib.rs:19080–19135`); candidate incoming routing selects
the graph branch (`19454`), so closed-scheme semantics are not a prerequisite
for these actual candidate extrusion roots.

## 5. Representatives preserve allocation and the exact association

The forest need not be total. `start_candidate_graph:2528` starts default empty
Value/Effect forests. `representative` (`candidate_intrusion.rs:119–128`)
returns an untracked row unchanged when it lies beyond the current forest.
Consequently a valid new row stays valid even before forest extension; an
arbitrary invalid row is not validated by this behavior.

Use the induction invariant: forest length is at most the allocated row count;
every stored parent is in that forest, and each tree has an in-region root.
`retain_extrusion_parent:310–365` extends each typed forest with identity entries
through the current row-table length before storing its actual copy/parent.
Those rows are the valid source and newly allocated same-kind copy at this
extrusion. Later fresh births may exceed the forest length without changing
this invariant.

`merge_candidate_rows:599–708` reads a previously stored Parent, takes both
representatives and rejects cross-kind pairs. Equality is a no-op. Otherwise
it connects one root to the other distinct root of the same typed forest.
That cannot create a cycle; both roots already name allocated rows. It copies
bound sides to the destination and retains the physical source row. Level
minimum/non-generic updates change metadata, not row membership. Compression
(`510–568`) rewrites parents only to the existing root. The only forest
truncation is rollback; it is outside this continued successful branch.

Thus canonicalization terminates and sends every valid typed row to a valid
row of the same kind. Applying this to section 2 gives, throughout successful
history, for a Value Component position j and t=component_terms[j]:

```text
value_endpoint(t, s)
  = value_endpoint(candidate_endpoint(Component(j), s), s)
  = ValueRow(value_rep(live_components[j].ordinal)) in V(S).
```

The equation relates translations in the current state; it does not assert
that the raw row equals its representative after intrusion. Effect components
obey the parallel equation in E(S). Parent/copy association remains attached
to its actual extrusion occurrence; this proof does not certify occurrence
qualification or SCC adequacy.

## 6. Bound emission, replay and the accepted schedule reach the roots

The actual emitter `candidate_insert_bound_with_evidence`
(`candidate_extrusion.rs:702–875`) checks the owner region and same endpoint
kind, but **does not check an item's row ordinal or structural term tag/sign**.
Readback equality after append is not such a check. The proof of those item
facts is the following producer induction, not emitter success:

| Producer of physical bounds/tasks | Preservation argument |
| --- | --- |
| `candidate_apply_value/effect:1115–1172` | Canonicalize the typed task; choose its actual row owner and other endpoint; section 5 preserves both regions |
| Signature Effect port (`candidate_effect.rs:2694`, `2725`, `2815`) | Owner freshly allocated; view created from an allocated Effect tail or None; no new Value term |
| Fresh bound restoration (`candidate_scheme.rs:4950`; `candidate_extrusion.rs:966–1068`) | Section 4 supplies mapped terms/rows and captured orientation; saved operations retain endpoints, then reread a canonical live owner |
| Extrusion source link and selected bound copy (`candidate_extrusion.rs:145–193`, `399–421`) | Same-kind fresh copy, valid original row and previously valid selected endpoint; structural rebuild preserves sign/kind |
| Intrusion merge (`candidate_intrusion.rs:635–656`) | Copies existing valid bound endpoints into the same-kind representative; keeps raw source storage |
| Context filter execution (`candidate_context.rs:4219–4305`) | Uses the task's existing lower and a view operand; it creates no new row or term; tail rows still come from view construction |

`candidate_signature_view:1219–1278` stores the supplied tail unchanged.
Actual non-test signature callers supply None, `candidate_formal_effect_variable`
or a fresh signature Effect variable (`2675–2824`). Copy/remap
(`1524–1567`) supplies the FreshUse Effect image or extrusion Effect copy.
Therefore every retained actual view tail is an allocated Effect row. This
is the only view-content fact used here. `candidate_register_capture_bound`
(`1035–1042`) registers the already valid row owner as incidence source and
canonicalizes that tail; splice only relinks records (`1011–1033`). It does
not generate a row from a view/member/payload number.

Selected bound enumeration reads actual direct/exact vectors
(`candidate_extrusion.rs:877–940`); mutation only appends valid endpoints in
this history. Replay (`1070–1113`) builds its task from the inserted bound and
actual opposite bound, in lower/upper order. `candidate_context_begin_replay`
(`4411–4499`) retains that task while adding relation children. Queue insertion
(`lib.rs:15328–15355`), typed-drain frame retention (`14394–14455`) and relation
transport (`candidate_context.rs:4186–4206`) preserve those endpoint values.
Structural dispatch (`lib.rs:14537–15025`) decomposes the actual visible nodes
with the constructor-prescribed variance; tuple/record/variant child vectors
come from those nodes, not synthetic row ordinals. A diagnostic is compatible
with this storage invariant and does not reset it.

The source action dispatcher (`candidate_source.rs:2469–2520`) covers every
Action variant. Fact/Link/ValueConstraint/Group/structure/Apply/Lambda actions
use sections 1–3. Module/Local/Operator actions use section 4; annotation,
formal-entry/record/unit, primitive, operation and Catch/FieldBoundV1 use the
same typed recipes/fresh caches. Begin/EndLambda/BeginLocal retain scheduling
state; WhereClause and DeferredFieldTail retain existing valid row references
without constructing a substitute row from an identity. Source Install and
LocalAnnotation retain the exposed term in PublishLocal before publication
(`2402–2467`); successful additions preserve it. Member-selected links retrieve
the exact graph interface rows through that use's own FreshUse map.

`execute:10702–10729` runs the SCC plan, Loose and expression schedules;
`execute_candidate_graph_plan` constructs provider/member captures in the
same session. Source drive advances only after action success. The non-test
receiving assembly also executes the same sealed actions (`candidate_receiver.rs:
5539–5589`). Its later effect publication consumes existing terminal endpoints
and the existing result row (`3200–3220`, `3254–3276`), introducing no raw
row/term construction. Failed route continuations are removed by R246, not
assumed repaired. These facts connect the invariant to actual work, rather
than establishing it only for a manually supplied valid work item.

## 7. Application at both calls and all visited structural children

At `lib.rs:14822`, the current typed pair has a non-row positive lower and
ValueRow(r) upper. Sections 1–6 give r in V(S), so the indexed target level
exists; the root lower has its claimed visible positive structure/atom.
The actual call supplies Positive and `value_levels[r]`.

At `lib.rs:14835`, ValueRow(r) is the lower and a non-row negative upper is
the root. The same derivation gives r in V(S), its level entry, and that
root's visible negative tag/sign. The actual call supplies Negative and the
lower row's level. These two calls, not hypothetical direct Effect-root or
arbitrary private invocations, are the applications of D-RT.

Inside `candidate_extrude`, induction over emitted Work tasks is now grounded:

| Work edge | Row/term fact supplied |
| --- | --- |
| Root canonicalization (`:94`) | Section 5 preserves root/receiving kind and regions |
| Row Visit (`:102–210`) | Level index exists; fresh copy belongs to the same typed region; Parent/link are actual valid row references; direct/exact selected children use section 6 |
| Function Visit (`:299–352`) | Visible tag and ports from the immutable term; argument Value/Effect flip sign, result Effect/Value preserve it |
| Tuple/Record/Variant Visit (`:224–297`) | Actual ordered children of the visible signed node; tuple arity/nonempty, Record emptiness and Variant's zero-payload alternatives use the current constructors |
| EffectView and incoming allowance (`:195–223`, `:354–398`) | The selected view's stored tail and incidence source are allocated Effect rows; mapped tail is the same-kind image; view/member/payload validity remains a separate W conjunct |
| Function/Tuple/Record/Variant completion (`:422–569`) | Reuse original terms for unchanged ports; otherwise translate valid mapped row/structural endpoints with the port sign and use checked constructors; retain actual tags, field metadata and ordered intervals |
| Bound (`:399–421`) | Insert the already valid copied endpoint into the valid copy owner; raw source BoundKey is not replaced by the child's canonical identity |

No row table or arena node is deleted by these successful steps. Work and bound
snapshots can observe later appended bounds; the invariant applies to every
appended endpoint, so it does not require a frozen entry snapshot. This proves
row/term closure for each actual visited child, independently of eventual queue
execution, settlement, acknowledgment or a global termination claim.

## 8. Classification and precise remainder

| Premise of the original entry edge | R247 class/disposition |
| --- | --- |
| Receiving Value row and level entry at both actual calls | DERIVED, sections 1–2, 5–7 |
| Source Parameter/Component range/kind and exact collected/native row association | DERIVED at actual producer positions, sections 1–2; arbitrary translator arguments remain unchecked |
| Arena visibility, live/structural tag/sign and actual child-port rows | DERIVED along successful histories, sections 2–4, 7; unrestricted rollback persistence rejected |
| Captured Row keys, FreshUse row images and reconstruction input lifetimes | DERIVED for this successful production history, sections 4–5; this removes the named R245 row/term retained-input premise |
| Representatives/physical bound endpoints/visited structural descendants | DERIVED, sections 5–7; no assertion that raw equals representative |
| Optional view tail and registered incidence source row membership | DERIVED row projection, section 6; full incidence/list/view correctness remains separate |
| Whole WCurrent / R245 current return theorem | CONDITIONAL on remaining WCurrent inventories and successful checked helpers; neither is renamed HRT |
| View/member/payload/context/evidence provenance and retained owner/head validity | OPEN beyond the explicit row/term projections above; exact consumers include extrusion `:195–223`, `:354–398`; FreshUse `:4660–4719`; context replay `:4411–4499` |
| Every raw bound slot has the needed canonical fiber (R71) | OPEN, independent; physical emission/readback does not prove it |
| Later typed drain, queue acknowledgments, intrusion settlement (R70-DRAIN-1), foreign continuations | OPEN, independent; retained/queued references are not completion |

No row/term constructor equation is left as an assumed successful-history
invariant in D-RT's stated production domain. This is a static constructive
argument, not an independently reviewed theorem or a Lean completion claim.
The next full-entry premise is the non-row inventory/owner conjunction, not
another proof that a live-variable node preserves its input ordinal.

Mutual TODO `R247-ENTRY-INVENTORIES-1`, owner Luna: retain the unchanged parent;
audit the actual view/member/incidence and retained-context/evidence owners
needed by the exact consumers above, using these row/term facts as established
candidate inputs after review. Required output: original-owner equations and
their application at both calls; falsifier: an accepted successful source prefix
reaches a real call/child with an invalid corresponding inventory reference.
Do not replace this with an origin-count/fiber-count equality or a queue
completion lemma. R71 and R70-DRAIN-1 keep their existing independent owners.

Implementation disposition **NO_SAFE_CODE_SLICE**: actual native translators,
physical bound emitter, forest merge and replay owners were read. Their weak
local checks are not a demonstrated reachable defect when producer invariants
hold. No accepted-source malformed row/term prefix was constructed, and no
production change is proposed on a hand-built state.

Reused: R245's exact Parameter equation and current structural case inventory;
R246-EXIT only for failed-route/non-continuation; formal-permission r3's exact
arena equations and rollback-offset caution, rechecked against current term
and wrapper owners. Their historical source pins/reviews do not review R247.
Rejected: tag/constructor success as ordinal validation, branding as occurrence
membership/uniqueness, HashMap insertion as duplicate rejection, equal numeric
Value/Effect IDs, raw/canonical identity collapse, independent FreshUse identity
collapse, copied metadata as evidence, and queue transfer as acknowledgment.

## 9. Execution and stop receipt

Checks were static source reads/searches, SHA-256 comparisons and read-only
baseline-ref observation. Initial `python` hashing command failed because
`python` was absent; it was rerun successfully with `python3`. Some combined
read output was truncated; the argument's allocator, native, capture,
reconstruction, forest, bound and source-index passages were reread in bounded
chunks. No runtime behavior is inferred from these commands. No Lean, builds,
tests, probes, Cargo, benchmark, external contact, Git command, production edit,
quarantined/runtime path, scratch/cache output or descendants.

Requested model/effort `gpt-6.1-sol/high`; observed model/effort UNKNOWN.
Actual worker `/root/sol_r247_successful_history`, current parent session
`01a1873a-a93b-7dc3-a8ce-028a7b543a80`; assignment and hash/admission collaboration
messages are the active-work receipts. Budget <=2400 active seconds. Initial
clock observation 2026-11-02 03:46:53 UTC; a final clock observation is recorded
in the handoff. Exact active CPU/time/RSS UNKNOWN; the full reservation remains
charged, with no unobserved refund, renewal or model switch.

All new/written paths: this note and the one assigned R247 inbox. Scratch NONE;
descendants NONE; unresolved descendant leases NONE. After final hashing,
revision 1 is **FROZEN / STOPPED / WRITES_STOPPED**. Fresh independent review,
adjudication, central records and integration belong to Luna. No continuing
worker or next-stage authorization is implied by this handoff.

## Frozen dependency appendix

The final manifest hashes follow. The theory hash is carried by the handoff;
the handoff hash is returned externally, avoiding recursive self-hashing.

```text
429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be  crates/yu-solver/src/lib.rs
6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e  crates/yu-solver/src/candidate_scheme.rs
bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49  crates/yu-solver/src/candidate_source.rs
80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61  crates/yu-solver/src/candidate_extrusion.rs
d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1  crates/yu-solver/src/term.rs
a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905  crates/yu-solver/src/candidate_context.rs
475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97  crates/yu-solver/src/candidate_intrusion.rs
4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15  crates/yu-solver/src/candidate_effect.rs
5ca308e7b890e57a8458a151554ece55585d762565204d39c520c4b534e44ade  crates/yu-solver/src/candidate_receiver.rs
99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5  crates/yu-solver/src/shadow_apply.rs
104720837d86a40efafe1676bf23d756042ce78355d0bfc84c69918aa7676956  tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r3.md
7ef7ca1bb40fbe18370691b064edc3b24d9818076dbb63738fdb3d6b6f72101e  notes/theory/2026-11-02-ordinary-extrusion-native-entry-and-return-r245.md
647860bfec8b9b7b7b1809ace66c24181e1c9ad8c7b3f7616c7100acdb439322  tasks/agent-loop/inbox/ordinary-extrusion-native-entry-and-return-r245.md
6ec2b144b1976eed7f3fe6e8a2a2ea65f9e23c1836980d288ae695f55a0a408a  notes/theory/2026-11-02-production-error-lifetime-r246.md
77c8f198805891c9dfd2b8c33f8b03fdda99169aef294138ff6684439734160b  tasks/agent-loop/inbox/production-error-lifetime-r246.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646  crates/yu-hir/src/module.rs
7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1  crates/yu-hir/src/module/local_source.rs
```

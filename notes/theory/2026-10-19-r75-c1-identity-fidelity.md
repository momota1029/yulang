# R75 C1 identity fidelity: equality construction and first coverage obstruction

Status: **STOPPED at an exact unleased reader premise; conditional construction, unreviewed**.
Author: `/root/r75_proof`, sole author; no descendants. Requested Sol/high;
observed model/effort UNKNOWN. Contract revision 1:
`tasks/agent-loop/sprints/c1-identity-fidelity-20261019-r75.md`, SHA-256
`7cfdd4c64031ad79d1b3de6bf9871d70e59832f9ab7f180c0410e723d7815156`.
Baseline supplied by Luna: `d21c8eb3a87e43dd441474c9f138e71b1d8372ff`.

## Parent application and actual result

The parent is computation-forwarding preservation §§1, 6–7 in
`2026-10-15-computation-forwarding-preservation.md`: one shared satisfying
assignment, original resolved declarations/formals, whole current-formal Name
arguments, arbitrary finite prefixes, repeated calls and simultaneously live
receivers. Native mapped-bound capture/admission, actual receiving/read/Force,
and independent F1/FK1 obligations remain OPEN. A faithful fixed C1 observation
would supply evidence for investigating those bridges, not prove them.
Full inference/evaluator and Simple-sub A/B remain OPEN 0→0; R50 remains
NOT_ADOPTED. Generation, accumulation, propagation, levels, extrusion,
qualifying intrusion and generalization retain their existing meanings.

Actual result: authentic equality supports family-separated identity labels,
and pinned HIR APIs support checked source joins. Complete field coverage is
blocked by the actual retained source Value graph's private identity maps.
`candidate_source::Plan.references` is part of the R74 SOURCE_PLAN snapshot;
its `candidate_value_graph::Graph.modules` is an actual
`HashMap<DefinitionRootId, DefId>` private to `candidate_value_graph.rs:11`.
That file has no R75 implementation lease. Its existing observation methods do
not enumerate this map. This is the first exact missing premise; no complete
R75 ledger, fixed-run certificate or implementation-specific erasure theorem
has been established. Luna acknowledged this obstruction and instructed freeze.

R74's ledger is incomplete. Both frozen R74 proof files contain the actual
revision-1 SHA `9b225304040b8ff11b1f1cb79876de136ce0400d69c68fef87bf07288f2c8a25`.
The R74 revision-2 claim that they mistyped that hash is factually false.
Neither R74 file is edited here.

## 1. Equality labels: a constructive conditional lemma

For each identity family F, retain a detached vector D_F of authentic typed
identity clones. On visiting x:F, search D_F using the actual F::eq; return the
index of its equal element, otherwise append x and return the previous length.
Emit a label (F,index). Never label by Debug, spelling, ordinal alone, endpoint
representative, source range, or a hash value. This finite algorithm needs no
new HIR identity constructor and does not mutate solver containers.

Invariant after k visits: D_F has pairwise unequal members; every visited x
has exactly one equal representative in D_F; its recorded label names that
representative. The empty vector establishes the invariant. An existing match
preserves it and returns the unique representative. If no match exists,
appending x preserves pairwise inequality and supplies its unique representative.
Induction proves, within one completed collector invocation,
`label_F(x)=label_F(y) iff x==y`. Family tags separate labels of distinct types;
repeated references preserve multiplicity in the traversal even though their
labels share dictionary entries. Allocation failure or an interrupted traversal
produces no complete certificate. First-visit order need not be stable across
runs, especially when traversing HashMaps; the lemma asserts equality fidelity,
not deterministic numbering or original insertion order.

Pinned equality implementations in `yu-hir/src/module.rs:283–483` supply:

| Family | Authentic equality operands |
| --- | --- |
| DefinitionRootId | HIR artifact pointer identity and structural DefId equality |
| HirOccurrenceId | HIR artifact pointer identity and occurrence ordinal |
| ExpressionRootId | wrapped authentic occurrence |
| SourceRootId | enum variant and the corresponding authentic root |
| HirLocalId | authentic SourceRootId and local ordinal |
| HirParameterId | authentic SourceRootId and parameter ordinal |

Keep ExpressionRootId, its occurrence, SourceRootId and its wrapped definition
as separate family entries with explicit linking fields. Coinciding Debug text
or ordinals do not identify them. DefinitionRootId's Debug omits both identity
operands; occurrence Debug omits its artifact; parameter Debug omits its owner.
These omissions directly invalidate treating R74 Debug text as identity data.

Other retained families must use their own authentic equality:
`DefinitionOrderId` has collection-artifact brand plus ordinal;
`DefinitionUseId` has collection brand plus authentic occurrence;
`ConstraintOccurrenceId` has authentic occurrence plus local slot;
`CauseId` wraps that constraint identity (`lib.rs:424–599`). SourceNodeKey,
DefId, SourceEffectId, SourceOperationId, LocalSourceIndex, named-group and
catch-binder IDs require separate typed dictionaries when reached. Solver row,
term, relation, bundle, context, evidence, source-event, use, replay-operation,
scope and region indices require owner/family namespaces and their raw values;
they are not interchangeable HIR occurrences or runtime receiver identities.
This is a construction theorem, not evidence that a collector enumerates all
these families or that all have an original HIR object as direct owner.

## 2. Owner dictionary: exact joins and their premises

For each reached HIR identity, retain its authentic value, checked owning HIR
object, and checked available source position. Joins must use the same immutable
HIR artifact and ShadowArtifact parse. `owns_definition_root` and
`owns_occurrence` test artifact brand only (`module.rs:1030–1037`); they do not
prove a matching registered source object or source-table entry exists.

A definition joins to a HirItem::Binding by authentic definition-root equality;
an expression root joins through `HirModule::expression_root` and the actual
expression item; a SourceRoot follows its enum branch. A local joins through
`local_source_for(local.source_root())` and `bindings()` by authentic local
identity. An occurrence joins to its actual ordinary or retained LocalSource
expression object by authentic occurrence equality, with an explicit owner;
`local_source_for` and `expression()` retain the constructor's source root/index
checks. A parameter joins to the actual binding parameter or LocalSource Lambda
parameter by authentic parameter equality, not just ordinal. Named headers
also retain formal IDs. Such enumeration must include nested Lambda parameters,
not only top-level binding.parameters(). Each successful table/object lookup
is a premise to record, not an implication of spelling or a brand predicate.

Exact positions use `ShadowArtifact::{definition_source_position,
occurrence_source_position,local_source_position,parameter_source_origin}`
(`shadow.rs:616–724`). These check authentic ownership, retained provenance,
parse ownership and exact SourceNodeKey lookup. `source_position` rejects a
foreign parse, missing key or ambiguous source (`:751–762`). For a parameter,
`parameter_source_origin` supplies IdentifierPattern or InlineLambda with its
exact lambda/binder; `parameter_source_position` deliberately rejects the
inline case. A successful lookup identifies the retained exact raw-CST position;
range and kind may then be read through `position`. Record every relevant
failure explicitly and reject a promised complete dictionary. Different HIR
identities may share one source node; source-position injectivity is not needed
and must not merge dictionary entries.

Thus successful checked joins certify each individual row's constructor-owned
provenance. They do not prove universal coverage. SourceNodeKey/annotation/
effect-declaration links and solver-index owner tables remain separate cases;
a solver row may be a copied allocation rather than an original syntax object.

## 3. Coverage audit and the first missing reader

The retained roots include LocalUse, complete GraphState (hence intrusion,
effect algebra and context), actual by_output keys/group vectors, typed-pair
memos, typed worklist, source Plan, and physical live value/effect bounds.
A coverage proof needs a structural traversal of every reachable identity field,
including map keys, values and repeated vector entries. A raw-state Debug dump
can accompany this traversal but cannot replace its authentic identity joins.

The following directly observed field groups must be included:

| Owner | Identity-bearing field group |
| --- | --- |
| GraphState / LocalUse | local_route_by_occurrence keys; locals.id; local_routes local/occurrence; routes.use_id; local_use local/occurrence; active root/use IDs under intrusion |
| Graph / FreshUse | graph bounds/evidence and attachment references; every raw row/term, effect operand, scoped relation, bundle/context/evidence remap and source scope/region/input reference |
| source Plan | definition_regions, occurrence_regions, local_regions, computation_scopes keys; scope_occurrences; schedules keys/actions; expressions.root/actions; source_owners keys/values; locals; omitted_formals keys/owner/lambda/formal/position/scope |
| source Action | every occurrence; AnnotationScope root/local/index; annotation owner/position/type/row/effect payloads; operation declaration/owner; handler field evidence when present |
| context | typed_drains occurrence/cause and pending work; inferred-entry lambda/occurrence/cause; bundles.occurrence; source_bundles keys/log; weights owner/position/allowed; evidence origins; replay/restoration state and undo logs |
| effect algebra | contributions effect/origin; views owner/position/allowed and operation provenance; formal permissions owner/occurrence/scope/source row/families; field evidence when present |
| source Value graph | modules keys/values; vertices keys; values_by_ordinal values; checking keys and checking_by_event entries, with their actual raw containers |

This table is an audit result through the first obstruction, **not an exhaustive
coverage certificate**. Empty or disabled scoped/handler branches require
explicit checked absence at this fixed cut; source syntax alone does not prove
that no retained records exist. Raw vectors, raw endpoints, source sets,
generations, map keys/group order, memo state, replay/restoration/undo records,
bounds and physical multiplicity must survive alongside identity labels.

The first obstruction is source Value graph.modules. `observed_value(ordinal)`
only queries values_by_ordinal/components; `observed_checking(event)` only
queries checking_by_event with a consistency condition (`candidate_value_graph.rs:
28–36`). Neither returns modules, and no reader enumerates its actual keys.
`register_module` inserts roots/DefIds (`:37–42`), but rebuilding a dictionary
from HIR proves neither equality with this retained map nor absence of extra
keys. Debug elides the DefinitionRootId operand. Consequently the required
identity fidelity of that actual map cannot follow from the current readers.

Minimal TODO R75-VALUE-GRAPH-READ-1: Luna should obtain an exact test-only lease
for `crates/yu-solver/src/candidate_value_graph.rs` via a revised contract and
add a detached immutable projection enumerating actual modules keys/values.
For the same owner seam, expose actual vertices keys/ordinals,
values_by_ordinal keys/values and checking_by_event in raw vector order rather
than infer their equality from point-query successes. Preserve map keys and
vector multiplicity; any sorting happens only on detached output. The minimal
falsifier is one actual retained identity map entry omitted, relabeled by
Debug/ordinal, or altered by the accessor. This TODO requests authority; it
is not permission to edit that file. Other owner-reader gaps may remain after
this first seam is repaired; they were not certified away.

## 4. Successful-path observer erasure and its current limit

Let S be the complete solver state at the fixed C1 hook and O a collector.
Assume O terminates successfully, reads S only through transitively pure
immutable access, writes only detached observer storage, and has no solver
control edge, mutation, interning, path compression, resource sampling, queue
advance or emitted solver work. After O's borrow ends, assume the unchanged
next statement pops the same LocalUse and calls the same Local step. Erasing
O leaves exactly the same S and subsequent solver transition. Induction on
subsequent unchanged transitions gives successful-path solver-state/output
erasure. Labels affect detached presentation only. Cloning Arc-branded IDs
preserves their identity equality; their temporary extra reference counts
are outside this semantic projection, provided no next solver branch observes
those counts or allocation addresses.

This lemma excludes allocator failure, panic/abort, observer TLS misuse,
process timing, allocation history, RSS and performance equivalence. It proves
no failure-path rollback. `&InferenceSession` alone does not prove transitive
purity in the presence of interior mutability or hidden side effects. The
actual finalized collector's complete call graph and its cut placement must
be inspected by fresh reviewers. The current R74 hook is after push/accounting
and before LocalUse's first pop, and uses detached TLS storage; its successful
run is prior fixed-source evidence only. It supplies neither R75 coverage nor
a proof about a not-yet-frozen R75 collector. Hence the general conditional
lemma is reusable, while implementation-specific erasure remains OPEN.

## Frozen inputs, checks and stop receipt

SHA-256 direct dependencies:

```text
parent                 d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79
inference principles   7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81
HIR module             c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a
HIR shadow             460c813cb0d2e21565df011b1d816abbc2b180cef13797a1b7b453e9ee413f66
HIR local source       ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5
candidate scheme       5529c61b3132e92d1dffa52ed230727760c47384c43f8910dd53f6228a419f93
candidate intrusion    7ff356632f3d665747d14ad1e0013a35c3a27e80de16564d5fefcdbf07ad14f2
candidate context      42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca
candidate source       66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c
candidate Value graph  8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50
candidate effect       6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0
solver lib             b90eeb2ce7ff78731ce418313fd9fb54b91283d90ae6462723186fde5c0045b0
R74 proof              08d7982542ce3119839c71405c2a78597bd124d4adc1050a9e66185ca06c92bb
R74 proof inbox        74d9d5f8ae831407a3020d647dd434bdf3fbef08a285330add5bffe83220ad3c
```

Prior work reused: R74's constructor cut and conditional erasure premises.
Rejected: R74 Debug completeness and the false contract-hash-mistype narrative.
No general theorem is imported outside its premises. Checks were static source
reads and SHA-256 only; no build, test, probe, Git, network or descendant.
Budget: one 600-second proof allocation; actual elapsed UNKNOWN, no refund
claimed. New/scratch paths: only this note and the assigned proof inbox, no
scratch files. Writer stops after their freeze; descendants none. Next action
belongs to Luna: adjudicate the exact reader lease revision, then supply a
frozen collector and independently reviewed coverage/erasure evidence.

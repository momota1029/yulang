# Module expression receivers: constructive level and use-routing prerequisite

Date: 2026-10-16
Status: algorithm-level construction and the actual implementation bridge in
§10 have fresh independent proof review CLEAN. The original native semantic
adequacy and default/production cutover parents remain OPEN.
Primary baseline: `1a64937f1`. Solver owners were read while stable; subsequent
compatibility-worker edits are excluded from this derivation. Additional reached
owner checks use the packet-authorized read-only `git show 1a64937f1:...`.
Concurrently edited HIR input was read only with the packet-authorized
`git show 1a64937f1:crates/yu-hir/src/module/local_source.rs`.
Exclusive lease: this file only.

Independent review: compiler-referee `ordinary_carrier_semantic` returned CLEAN
at producer SHA-256
`2d45022a006db101a765fc97ae86c8187a2d265cfd1d9dc79f8d7e42c8f139e0`.
Pinned source inspection covers all constructor levels, publication scheduling,
original uses/Value association and annotation/view/context source ownership.
This accepts the algorithm-level prerequisite, not its unimplemented source
correspondence or full native inference adequacy.

Actual-bridge review: compiler-referee `ordinary_carrier_semantic` returned CLEAN
for §10 at producer SHA-256
`df8f57fc0417d39b5b9e19a16ae3998d50cd1f5dbd1a96c271b8d6d3f59df092`.
The ten solver and six HIR hashes matched, and the independently accepted G2
producer was consumed at its recorded hash. This closes the bounded actual
receiver/use/level/publication/Value/context construction correspondence;
it does not promote all-xi Function semantics or the default inference route.
Sections 1–9 retain the preimplementation snapshot; §10 supplies its later
actual-source bridge.

## 1. Authority, quantifiers and exact claim

The Authoritative [module-expression owner design](../design/2026-10-16-module-expression-source-owner.md)
selects an authentic ExpressionRootId, SourceRootId and

```text
SourceReceiver = Definition(DefinitionOrderId) | Expression(ExpressionRootId).
```

Direct expressions retain actual occurrences and source order, have body
level1, consume published definition interfaces through the existing use
owner, enter no definition SCC, and export no definition result scheme.
The [direct-root HIR slice](../design/2026-09-20-hir-direct-root-expression-slice.md)
adds no binding namespace entry or DefId. The
[ordinary carrier](../design/2026-10-10-ordinary-hir-successor-carrier.md)
retains original admission, identities and errors; the new decision extends
its source-root domain without changing the old binding claims. The
[top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
require generation/accumulation before solving, ordinary level/copy operations,
and exact occurrence-qualified source Value associations.

Quantify over every authentic direct-expression carrier admitted by the
approved carrier grammar, every supported finite constructor tree in it,
and every module-definition reference resolved by the original completed
namespace. Include nested Lambda, local binding, Catch, If, operation,
annotation and wrapper forms; there is no integer/Name/Apply-only restriction.

The theorem below constructs a receiver-parametric extension of the existing
source planner and a sufficient execution order. Its conclusion is:

1. Each original source constructor generates its existing constraints and
   identity associations with its actual expression owner and nested level.
2. Each resolved module Name retains its actual DefinitionUseId, target,
   occurrence/cause, component positions and syntactic use level.
3. An expression-origin use consumes only an authentic published target using
   the existing capture/FreshUse/route operation. Its local-copy and shared-
   anchor rules are those of that operation, with no extra Name algorithm.
4. The definition SCC domain and expression result nonexport are preserved.
   Forward references can be scheduled without fake definitions or changing
   their use identity.

This is an algorithm-level construction to implement, not an assertion that
baseline already accepts SourceReceiver::Expression. It proves the decisive
level/routing feasibility invariant. Actual source-to-code correspondence,
verification, supported-source inference coverage, runtime mixed-root order,
full source/native interpretation, soundness and principality remain OPEN.
The original all-xi/z FIRST-RESULT-ADEQUACY parent is unchanged.

## 2. Existing owners and the precise current blockers

`candidate_source.rs::emit_candidate_source` currently takes a DefinitionOrderId
and ends by selecting `root_component_positions[source.definition_root()]`,
emitting a definition root link/annotation and storing a definition-keyed
schedule (`:540–545,1108–1130`). This is the ownership seam to generalize.
Its structural Work visitor already starts at1, preserves levels through
Lambda/wrappers/branches and increments block initializer levels (`:650–815`).

`DefinitionUse` retains parent, target, original occurrence/cause, use_level
and frozen component positions (`lib.rs:624–675`). Collection currently
reconstructs every parent by `pending.parent_ordinal` and reads each actual
Name component's level (`:1295–1355`). Merely casting an expression ordinal
to that parent would be invalid.

`SccPlan::build` validates every parent as a definition and obtains its node
from the definition map (`scc.rs:245–281`). Expression uses must remain in
the batch's authentic use registry while being excluded from this definition-
edge input. Dropping them from the registry would lose actual use/cause
provenance; adding expression nodes would change the selected SCC relation.

`InferenceSession::execute:10378–10387` runs candidate loose actions **before**
the SCC plan. An Action::Module immediately invokes route_incoming, and the
candidate route requires `graphs[target]` already present. Therefore placing
new expression actions in current `loose` is unsound scheduling, even for a
textually backward Name: target collection is not target publication.

`candidate_value_graph::Graph::retain_source:69–77` currently seeds the owner
through a definition-root-to-Module mapping. Its new expression branch must
seed Value::Expression(original direct-root occurrence), not the referenced
module Name's target and not an invented Module value.

These are required code changes, not a contradiction in level1.

## 3. Construct the receiver and immutable source recipe

For each actual supported expression outcome form one receiver record with:

```text
authentic SourceRootId::Expression(e)
original direct-root occurrence and its supported LocalSource
original body source index
actual root value/effect component positions
body level = 1
source-order schedule position.
```

Authenticate e with the original HIR's expression-root/carrier lookup. The
carrier, all local/parameter/Catch/group owners and original occurrences must
belong to that same source root/artifact. This uses G2's honest root contract;
G3 does not construct an ExpressionRootId from a child or integer ordinal.
A foreign artifact or missing original root fails before source actions or
use facts become visible.

Build component positions with the existing occurrence-based allocator.
Reuse an existing authentic component for the same original occurrence, as
current collection does. Keep the body/root components without imposing
`result <: Unit`: discarded expression results are not required to have Unit
type. A direct ascription remains its actual source Ascription constructor,
not a fabricated binding annotation. No result generalizer, DefinitionOrderId,
root scheme identity or exported Graph slot is created for this receiver.

Generalize the consuming-parent field of PendingDefinitionUse/DefinitionUse
honestly to SourceReceiver. DefinitionUseId remains the same batch-branded
original HirOccurrenceId; its cause remains DefinitionUseCause::for_use(id).
The target remains the original collected DefinitionOrderId. The frozen use
component comes from that actual Name occurrence, and use_level comes from
its generated component-level map. Validate expression parent ownership and
its occurrence-to-carrier association during collection, separately from
collection-artifact ownership of the use ID and target definition.

Source-root fields currently typed DefinitionRootId must be generalized only
where expressions actually own source: schedules/regions, original formal
registrations, Apply source inputs, operation-use provenance, annotations and
observers. Definition targets and their published scheme roots remain
strictly definition-owned. A definition-only accessor cannot return a fake
root for these new records. In particular the observer at
`shadow_apply.rs:777–786` must match the consuming-parent variant instead of
indexing `definitions[parent.ordinal()]` unconditionally.

### Annotation, view and context owners are part of this construction

Receiver lifting also reaches the existing annotation pipeline; a checked
definition-only adapter is an honest compatibility boundary, not completed G3
support. At the pinned source, `candidate_effect.rs:159–176` gives
`SignatureContext::owner() -> &DefinitionRootId` and `View.owner`, while
`candidate_context.rs:118–125,150–158` gives `LocalWeight.owner` and
`EmptyAttachmentSet.owner` (the latter is retained inside an
`AttachmentBundle`). Signature generation copies `context.owner()` into views
at `candidate_effect.rs:1576,1598,1663`; empty attachment construction retains
the annotation owner at `:1396–1420`. These are actual reached source fields,
including inert provenance, rather than optional receiver metadata.

For an annotation belonging to this expression carrier, carry its authentic
`SourceRootId::Expression(e)` through SignatureContext, View, LocalWeight and
the bundle's EmptyAttachmentSets. Keep its original source position, lexical
scope, resolved allowed members, tail and attachment polarity unchanged. The
existing signature recursion and context constructors then consume the same
allowed operands and construct the same constraints at the same levels; only
the honest source-owner variant differs. Every owner check must compare that
variant with the original carrier, rather than refuse an expression solely
because `definition_root()` returns None. Definition-owned signatures retain
their original Definition variant.

Operation signatures have two distinct identities in that same pipeline:
`SignatureContext::Operation.owner` is the consuming expression's provenance,
whereas `OperationOrigin.declaration` and each resolved SourceEffectId refer
to the original effect declaration. Lift the former to SourceRootId without
retargeting the latter. An expression occurrence does not declare a new effect.
The proof does not erase an ownership check or replace resolved allowed members
with spelling equality. The same distinction must be preserved when retained
views/weights are copied: fresh row maps act on inference coordinates; they do
not turn the expression root into a declaration identity.

Consequently already supported annotation constructors are included in the
constructor induction below. Mechanical G2 adapters which deliberately refuse
an expression owner are expected incomplete implementation paths, and must be
removed by this G3 receiver lifting before correspondence can be claimed.

## 4. Constructor induction proves the level invariant

Define L on the actual source tree, beginning with L(body)=1. The exact
existing constructor clauses are reused:

| Constructor | Level and generated ownership obligation |
| --- | --- |
| Unit, Integer, Boolean, String | Value/effect components at current L; original literal/source occurrence retained. |
| Name | Its occurrence components at L; original resolution selects ModuleDef, Parameter, Local or CatchBinder. Module Name use recipe retains this L. |
| Operation | Original declaration-derived signature and target components at L; code provenance belongs to this source root, declaration identity stays its original declaration. |
| Apply | Callee, whole argument and result/effect components at L; actual callee/argument/result/checking occurrence retained. |
| Group | Child remains at L; actual Group constructor preserves its own source occurrence and existing facade rules. |
| Ascription | Child and actual annotation construction at L; original source scope and ascription identity retained. |
| Lambda | Parameter and body at L, exactly as baseline. Named-group information does not invent a level increment or dynamic owner. |
| Block | At current L, each initializer is visited at L+1 and its LocalScheme is installed at boundary L. Final expression remains at L. |
| If | Every condition and every branch, including an omitted-else case's existing rule, is generated at L. No branch is skipped by evaluating a condition. |
| Catch | Scrutinee and arm bodies remain at L. Actual Catch binder introduction level is L; a later nested initializer read does not raise the binder's original level. |

Induction on these clauses proves L>=1 everywhere and the same local
initializer/boundary relation as binding-owned source. Group/Ascription may
share component positions according to existing normalization, but their child
level is the same; that sharing cannot turn a module Name's use level into0.
Catch-binder representative levels follow the existing introduction rule,
while a module Name's use recipe still records its own occurrence component.

The only arithmetic increment is checked L+1. Exhaustion is an availability
failure, not a reason to admit a partially planned receiver. The scope and
level proof covers all carrier constructors in the table; it does not assume
a particular final type, prior execution, effect support or successful solve.

### Existing preflight is a separate outcome, not a hidden shape restriction

A HIR Supported(LocalSource) is broader than current solver preflight. At
`candidate_source.rs:394–453`, unresolved/ambiguous Names and certain existing
annotation/operation/Catch-signature cases produce the current explicit
refusal. G3 must preserve those existing outcomes and HIR errors, not relabel
all Supported carriers as successfully inferred. Unresolved Names create no
resolved definition target/use. The receiver extension adds no new refusal
based on its expression root or on a constructor's shape. Wherever the
existing constructor accepts, the generated action/level rule above applies;
where it refuses, preserve that exact availability/unsupported boundary.
Broader existing inference coverage remains an explicit gate, not a narrowing
of approved ordinary source behavior to make this theorem succeed.

## 5. Published-target scheduling: a sufficient construction

Keep the original definition dependency SCC plan, using only uses whose parent
is SourceReceiver::Definition. Definitions still follow dependency-first SCC
order. Same-SCC uses keep their existing active-root route; external definition
uses keep their existing published-target route.

After this plan completes successfully, execute expression receiver schedules
in their retained source order. This is a sufficient G3 schedule, not a new
runtime evaluation order. No module Name can target a direct expression,
because expression roots have no binding namespace entry. Hence expressions
introduce no dependency needed to publish a definition graph. Every resolved
expression target is among the already published definitions at this point,
including a textually forward target.

Proof of availability: the finite definition SCC DAG has completed its member
source schedules, staged every member graph, then published those graphs
(`candidate_scheme.rs::execute_candidate_graph_plan:947–1037`). Expression
uses were excluded from its edges, so they cannot introduce an unfinished
expression dependency or alter its component membership. The target graph is
therefore available before the first expression Action::Module. Failure in
definition construction prevents this successful route and propagates through
the normal availability/error handling; no uninitialized graph is used.

An alternative incremental scheduler may start an expression earlier and stop
at an unavailable target, but then it must retain the **original** receiver,
action cursor, DefinitionUseId and frozen components until publication. It
cannot advance the cursor, synthesize another use, route an active unrelated
definition or regenerate the source actions. This packet proves the simple
post-definition schedule and does not assume an absent incremental deferral
mechanism. Current pre-SCC loose scheduling is not that mechanism.

Inference may generate all expression constraints without evaluating source
roots. G4's runtime execution list must still interleave computed binding and
expression demands in original HIR order, with ModuleRun/Invocation ownership.
The G3 order above supplies no runtime cache, result or handler-owner rule.

## 6. The decisive level/copy invariant at a module Name

Let a resolved Name n occur at its original level L>=1 in expression receiver e.
Let d be its authentic target definition, whose interface is published. Keep
the same DefinitionUseId, cause, target root component and Name component.
Invoke the existing `route_incoming(id)`; in candidate mode it delegates to
`route_candidate_graph` (`lib.rs:16576–16605,16796–16806`;
`candidate_scheme.rs:1058–1095`). That owner reads **only the target's actual
published Graph** for its live_root/boundary and recaptures from that root.
It does not select a definition from the expression receiver.

Preparation then uses this Name's L as use_level. For each canonical row q
in the captured target view:

```text
if q is local, level(q)>capture_boundary and !non_generic(q):
    mu(q) = one fresh row of the same kind at level L
else:
    mu(q) = the exact current representative q.
```

This is the actual `prepare_candidate_fresh_use:1095–1140` rule. Its one
canonical rows map reuses the same image on repeated occurrences and all four
Function fields. It neither fixes every nested Name at1 nor ages expression
uses to0. Shared anchors stay exact; local fresh rows have the proper consuming
level. Nested local references continue through the existing LocalScheme
capture at boundary B and use at their own generated L, without an exported
expression scheme.

`begin_candidate_fresh_bound` maps both endpoints through that same FreshUse,
keeps captured owner/side and exact original source BoundKey/evidence, and
restores every captured bound before root publication. The `route` owner
admits the actual fresh root to this Name's component and retains its actual
DefinitionUseId/fact once (`lib.rs:16957–17025`). Its use/cause validation still
precedes publication. SourceReceiver affects parent provenance/scheduling;
it does not change the target root, substitution, instance map or constraints.
Thus a second Name-instantiation algorithm is unnecessary.

This theorem is a construction/level statement. It inherits the existing
capture/FreshUse semantic and temporal obligations; it does not assert that
retained constraints alone prove full source Call, hygiene or principality.
In particular it establishes no new inverse from rendered types or row IDs.

## 7. Exact Value-reference associations and SCC separation

Register the direct source root as
`Value::Expression(e.original_occurrence)`, even when its body is a Name of d.
In `Graph::retain_source`, initialize the traversal's root owner to this Value.
Keep existing owner changes for local initializers: those use their actual
`Value::Local(HirLocalId)`. Parameter and Catch-binder Values retain their
original source IDs. All registered Name edges keep their original targets.

For every Apply at occurrence u, keep the existing association constructor
(`candidate_value_graph.rs:155–173`):

```text
origin   = actual owner assigned by this source traversal
receiver = expression_value(actual callee)
checking = ConstraintOccurrenceId(original u, slot0).
```

`expression_value` retains the established Group/Ascription peeling and
resolved Name target rules. Root registration does not replace the callee's
receiver. An Apply root can already have an Expression Value with that same
authentic occurrence; interning reuses that Value rather than inventing a
second root identity. A root Name's owner remains the expression occurrence,
while its referenced target remains Value::Module(d). This distinction is
exactly what a fake consuming definition or target-as-owner shortcut loses.

The existing Name/Apply/If fragment construction still projects precisely to
its original Name incidences. Extend its root owner input, not its selected
fragment relation. Seal the Value graph after registering all source roots
and edges, and let the existing occurrence-qualified extrusion/intrusion rule
consult these actual origin/receiver pairs. No solver-row SCC substitutes for
that source Value SCC.

Definition SCCs contain only actual definitions and their definition-parent
uses. Value-reference SCCs can additionally contain these expression/local/
parameter/binder Values. Old definition source cannot resolve a module Name
to a new expression root or its private local IDs. With authentic disjoint
root occurrences, adding expression trees therefore creates no new return
path from an old definition into an expression tree. It cannot merge old
Value SCCs through a fabricated expression namespace edge. Cycles genuinely
inside a new local source remain available to the existing Value algorithm.
This claim does not equate the honest expression graph with a hypothetical
synthetic-binding graph; their root Values are deliberately different.

## 8. Concrete owning handoff and postimplementation obligations

| Owner | Required implementation fact to verify |
| --- | --- |
| HIR G2 carrier/source identity | Authentic SourceRootId::Expression, original direct-root occurrence, all nested source owners and atomic outcome; no binding identity consumed. Moving worker output is not certified by this theorem. |
| `ConstraintBatch::collect_mode` receiver/root setup | Register one expression receiver with actual value/effect positions and level1; retain source order; preserve definition tables and export indices. |
| `emit_candidate_source`, Plan/AnnotationScope/call provenance | Accept honest source receiver/root; run every existing constructor; store its schedule and root components without a definition terminal export. |
| `candidate_effect::SignatureContext::owner`, View; `candidate_context::LocalWeight`, EmptyAttachmentSet/AttachmentBundle | Carry authentic SourceRootId through all reached annotation/view/context provenance, positions and lexical scopes. Remove receiver-only definition projection/refusal for already supported constructors; retain declaration-owned SourceEffectIds and operation declarations unchanged. |
| PendingDefinitionUse finalization | Validate actual expression parent and original Name membership; retain the existing use ID/cause, target, components and actual nested level. |
| `SccPlan::build` input partition | Only definition-parent uses enter definition adjacency; all expression uses remain authentic batch records with validated targets. |
| `execute` / source schedule driver | Run expression schedules after target graph publication; do not put them into current pre-SCC loose actions. Preserve receiver/cursor/use if an authorized incremental variant waits. |
| `route_incoming` / `route_candidate_graph` | Same published target capture/FreshUse owner and once-use provenance, with SourceReceiver only as honest parent. |
| `candidate_value_graph::retain_source` | Root Value::Expression(original occurrence), exact existing Name edges and Apply origin/receiver/checking association; no target-as-owner substitution. |
| Candidate observers/diagnostics | Match parent/source-root variants honestly; no unconditional definitions[parent.ordinal()] lookup for expression uses. |
| Finalization / G4 handoff | No expression definition scheme/cache cell; retain actual expression components and source order for the separate runtime root list. |

Correspondence must check all constructor cases, nested use levels, older/shared
anchors, forward targets, and recovered/unsupported outcomes. Cross-artifact
root/occurrence rejection must precede use admission. Existing type errors may
continue meaningfully; availability failure must not publish an inconsistent
receiver or route. No exhaustive rollback/capacity theorem is added.

There is no level/copy counterexample in this construction. The concrete
baseline blockers are missing honest receiver ownership/partition and the
pre-SCC loose-phase target-availability seam. A direct expression `d` already
falsifies the shortcut "collected target implies route-ready" whenever d's
graph has not been published; no source shape restriction repairs that seam.
G3 implementation stays OPEN until the above source-to-code facts, focused
verification and independent review are completed.

## 9. Checks, resources and commit packet

One bounded static constructive pass, approximately 25-minute allocation.
Commands: bounded `cat`, `sed`, `rg`, `wc`, hashes, and the explicitly authorized
read-only `git show 1a64937f1:.../local_source.rs` for stable HIR input. No Git
mutation, tests, builds, probes, network or delegation. Some guessed SCC file
locators were absent; corrected inspection used `scc.rs`. No result depends
on the failed locator reads. Only this note was written; zero heavy processes
or measured samples; CPU/RAM and exact elapsed time uninstrumented. Requested
normal Sol/high; effective runtime metadata unavailable.

Claim class: constructive algorithm-level prerequisite plus exact existing-owner
handoff; not postimplementation correspondence or production closure. Independent
review pending. Sole changed path:
`notes/theory/2026-10-16-module-expression-receiver-construction.md`.
Baseline `1a64937f1` supplied by primary. Concurrent HIR implementation and all
shared records remain primary/worker-owned. No current moving HIR source was
used to certify a completed implementation.

Governing input SHA-256 at freeze (source owner citations are pinned to
`1a64937f1`; moving compatibility code is excluded):

| Design input | SHA-256 |
| --- | --- |
| 2026-10-16 module-expression source owner | `9a48f9ce4bee6e533cb0198d4112803dff927df71f5bca6bec084ced204dcd66` |
| 2026-09-20 direct-root expression slice | `e2ca3943817e70de5b51bf432d696e3b3fdf90d85539e92ba429c6102691237b` |
| 2026-10-10 ordinary HIR successor carrier | `c5fb75bdeb302a1f490398589b823f26d296d4cff3889cd0fddd5be4f801dad1` |
| 2026-10-11 inference top-level principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

Proposed checkpoint:
`research: derive module-expression receiver level and published-use construction`.
Shared-record delta for primary/curator: record level1/nested-level feasibility,
exact expression Value ownership, definition-use SCC partition and the required
published-target schedule; retain G2/G3/G4 correspondence and broader original
inference/source-semantic gates OPEN. No shared record was edited.

## 10. Actual frozen G3 constructor and consumer bridge

Date: 2026-10-16. This append applies the preceding reviewed algorithm-level
derivation to the primary's frozen G3 implementation. Sections 1–9 retain their
original statement and historical implementation status. The claim class of
this append is source-to-implementation correspondence for that construction,
with fresh independent proof review pending. It does not close the original
all-xi/z native semantic parent or assert candidate/default cutover.

### 10.1 Inputs, scope and actual entrypoint guards

Consume the independently CLEAN [actual G2 carrier correspondence](2026-10-16-module-expression-carrier-correspondence.md)
at producer hash `57ba5d19388ad30fce91fb3368bd6e07032336c4c3dd62175b52df6e7211f085`
and its six unchanged HIR owners. G2 supplies original direct-root occurrence
authenticity, same-root nested identities, complete source outcomes and exact
ordinary namespace provenance. This bridge adds no assumption of a complete
native semantic interpretation.

The original quantifiers in §1 remain: all authentic supported source
constructors, all resolved module references and actual nested levels. As
already distinguished in §4, HIR Supported is broader than candidate inference
preflight. The bridge proves actual construction on its existing admitted
paths and preserves the existing refusal/error paths; it does not silently
reinterpret every structurally Supported carrier as semantically admitted.
`candidate_source::preflight:401–453` still checks every annotation/formal,
operation/Catch signature and unresolved/ambiguous Name. No expression-owner
shape restriction was added to those tests.

Actual source inference is selected by `shadow-apply-candidate`, candidate
values and candidate graph effects (`lib.rs:1159–1176`). The public candidate
`CandidateInference::solve_mode` first authenticates the original root and source,
runs that preflight, and permits only existing UnsupportedExpression carrier
placeholders; unrelated HIR errors, including recovery diagnostics, remain
rejection evidence (`shadow_apply.rs:271–311`,
`candidate_source.rs:513–530`). An Unsupported/recovered carrier does not
silently become an expression receiver: without a source, the existing public
fallback accepts only its already admitted legacy forms. The private collector
may retain legacy loose actions, but this is not a new parser or semantic
admission path.

Default `ConstraintBatch::collect` still chooses candidate_values=false, and
the legacy candidate wrapper chooses graph_effects=false
(`lib.rs:921–944`). These paths do not construct expression source receivers.
Default builds and definition-only observer adapters therefore do not certify
this feature's execution. Conversely their guards are honest partial APIs:
an expression has no definition export and cannot be queried through a
definition-only scheme adapter. Existing scoped-experiment refusals remain
separate and are not used to narrow the unscoped construction theorem.

### 10.2 Authentic receiver, original use identity and forward endpoints

During the original item traversal, collection allocates DefinitionOrderId and
definition/root/scheme positions only for Binding items (`lib.rs:1019–1154`).
For an Expression, it asks the original retained HIR for the authentic root at
that exact item's occurrence. It obtains local_source_for(SourceRootId), then
constructs SourceReceiver::Expression(root); a binding instead receives its
actual existing DefinitionOrderId (`:1161–1183`). No expression increments the
definition table or manufactures a result root.

`emit_candidate_source:551–565` first retrieves this source from its own HIR,
requires pointer equality with the supplied source, and matches the receiver
and owner variants exactly. A Definition receiver additionally matches both
the collected definition identity and original root. A foreign/mismatched
expression handle therefore fails before actions or pending uses are emitted.
The same source's original occurrences are registered in source_owners only
after artifact checks; conflicting ownership is rejected (`:566–572`). G2's
disjoint occurrence/root construction supplies the successful membership
premise, including the original expression body occurrence.

For every ModuleDef Name, Work::Finish pushes the original occurrence with
the original resolved DefId and parent.clone(), together with one Module
action (`candidate_source.rs:959–963`). After every module item has been
collected, the endpoint pass resolves that target against the complete actual
definition table (`lib.rs:1320–1353`). Thus forward references need not be
present in that table when the Name recipe is first generated. Definition
parents are checked against their actual table identity; expression parents
are checked against source_owners at the original Name occurrence. This is a
source-membership check in addition to an artifact brand check.

`DefinitionUseId` still consists of the same collection artifact and original
Name occurrence. Its cause is still for_use(id); target remains the original
DefinitionOrderId; Name and target-root components are the existing frozen
component-map entries (`lib.rs:1354–1386`). Only parent has the honest tagged
type. Each generated Module Name was visited with an actual level and entered
the component-level map, so its frozen use_level reads that level, rather
than relying on the compatibility fallback1. Duplicate use identity is still
rejected at the original map insertion. The identity is independent of the
parent's tag and target publication time.

### 10.3 Root components, actual ascription endpoint and every level case

The emitter allocates every occurrence component, parameter/formal registration
and local slot from the authenticated source (`candidate_source.rs:574–638`).
It resolves Ascription aliases before initializer links: an Ascription follows
only its actual nested Ascription/Group chain to the canonical child, then
aliases both its positions and endpoint to that child's positions/endpoint
(`:639–655`). It also updates the actual occurrence-component map. An ordinary
standalone Group retains its facade and existing Group relation.

The traversal starts at Work::Visit(body,1,region) (`:680`). The induction from
§4 applies to the actual Work clauses at `:681–850`:

- literal, Name and Operation occurrences use their current L;
- Apply children, Group/Ascription inner, every If child and Catch scrutinee/arm
  retain L;
- Lambda records its parameter level L and visits its body at L, while source
  region nesting remains a separate relation;
- each block initializer is visited at checked L+1, its local scheme boundary
  is L, and its final expression remains at L;
- an operation Catch binder representative is introduced at arm L; a deeper
  Name does not overwrite that older representative's introduction level.
  A value binder retains its actual scrutinee endpoint. Neither case asserts
  that every aliased endpoint is newly allocated at the Name's syntactic level.

The component map uses the existing representative rule for values and records
effects at their actual visit level (`:690–694`); parameter levels are recorded
at their actual Lambda clause (`:715–718`). Each Module Name has its own value
component, so the representative exception cannot substitute an arm/formal
level for a Module use. No expression-specific transition forces nested uses
back to1 or gives a fresh root level0. `initialize_candidate_source_levels`
installs these actual levels into live Value/Effect rows and parameter rows,
then initializes formal native roots and computation entry effects from those
same registrations (`:1202–1236`; called before execution at `lib.rs:10174–10175`).

Finish uses the existing constructor actions for primitives, Name, Operation,
Catch, If, Apply, Lambda, Group, Ascription and Block (`:853–1137`); local
installation retains its existing initializer effect and L/L+1 boundary
(`:814–849`). The consuming parent only annotates provenance and pending uses;
it does not select different primitive/Function/Effect/Allowance constructors.
Explicit Ascription actions constrain the canonical child endpoint directly
and keep the original annotation/cause/scope (`:1051–1089`). In particular a
parenthesized ascription is not checked against an unused outer facade.

For an expression body, same-level wrapper descent establishes that the
canonical peeled root components still have level1. If the peeled child is a
Block or Lambda, peeling stops there; it never descends into an L+1 initializer
or a Lambda body. `ExpressionSchedule` stores exactly positions[body] and the
final endpoints[body], including the Finish-time endpoint refresh needed for
Catch binder aliases (`:1163–1167`). Its executor validates original ownership
and both retained root component levels, obtains the actual positive endpoint,
then executes that schedule (`:1239–1247`). This is not a root-facade assumption.

The definition terminal branch still emits its old link/annotation to its
definition root and stores its old schedule. The expression branch emits no
definition terminal link, generalized result, scheme slot or exported graph.
It stores its body endpoint/effect components and actions only. Candidate
export graphs remain sized and published by the actual definition table
(`candidate_scheme.rs:762–766,947–1046`). Discarding an expression result does
not add a Unit result constraint.

### 10.4 Actual SCC partition, target publication and the shared FreshUse

`SccPlan::build:245–273` still validates every use artifact/target and rejects
duplicate use IDs. It selects only Definition-parent uses for definition
adjacency. Expression-parent uses validate that their target is a real
definition node and remain in the batch use registry; they add no SCC node,
arc or internal-use membership. Definition ordering and edges therefore retain
the relation used by §§5–6, rather than relying on an ordinal cast.

`InferenceSession::execute:10410–10429` now completes execute_scc_plan before
any loose or expression source schedule. In source mode, candidate graph-plan
execution runs every member schedule, captures every member at boundary0,
stages all member graphs, then publishes them and clears active roots/uses
(`candidate_scheme.rs:947–1046`). Induct on its dependency-first SCC list:
all prior target graphs are available to a member; internal uses observe the
established live roots; every member graph is published before the next
component. At completion every collected definition target has a published
graph, and no active internal-use set remains. This covers even a module with
no definitions: then an admitted expression has no resolved module target.

Only after that point does execute run loose compatibility work and then the
expression vector in its retained source order. Module actions use the
original DefinitionUseId; expression uses cannot satisfy the active-use test
and therefore call the existing route_incoming (`candidate_source.rs:1368–1374`).
The schedule Frame retains its exact schedule, next action, local publication
stage and support wait state (`:1256–1345`). No source rescan or new Name
instantiation rule replaces that cursor. This establishes the availability
schedule from §5; merely collecting a target is no longer treated as publication.
The static inference order is distinct from G4's runtime mixed-root order.

`route_incoming` validates the same use and enters the existing transaction
(`lib.rs:16616–16635,17122–17132`). Its candidate branch calls the existing
`route_candidate_graph`, which reads the published target's actual live_root
and boundary, retains its frontier and recaptures that current target
(`candidate_scheme.rs:1059–1081`). It then runs the same freshen/restore path
with record.use_level, original occurrence/cause and Name component
(`:1084–1104,1428–1475`). There is no expression-specific graph-copy branch.

The decisive row loop at `:1135–1150` canonicalizes every original row once
under one map. A local row above the actual capture boundary and not marked
nongeneric gets a fresh row of the same kind at the actual use level; otherwise
the exact canonical source row is shared. Repeated canonical coordinates reuse
the same mapped row. All nodes, bounds and context operands use that common
FreshUse. All captured bounds are restored before route publication
(`:1090–1094`). Thus both fresh local and older/shared/nongeneric cases of §6
are implemented, including later live information visible in target recapture.
This uses the existing FreshUse/replay invariants; it does not infer a new
complete semantic transport theorem from storage alone.

Finally instantiate_candidate_graph calls the original route owner with that
fresh root and actual Name row. `route(:16996–17078)` admits the original
occurrence fact/cause, constrains that pair and records one use/provenance;
the FreshRoute retains the actual use ID, graph and row map. Its once-use
assertion is met because source Work emits one Module action per unique
resolved Name, expression uses are excluded from SCC routing, and this
expression schedule is run once. Failures retain the existing transaction or
consuming-run abort behavior, not a new expression retry guarantee.

### 10.5 Exact Value associations and full source-owner propagation

`candidate_value_graph::retain_source:69–76` now seeds an expression root as
Value::Expression(original root occurrence), while definitions retain
Value::Module(original DefId). The existing source traversal assigns each
nested initializer its authentic Local Value; all other nested ownership,
resolved Name edges, fragments and original occurrence-based results retain
their established construction (`:77–158`). For every Apply it records the
actual source owner's Value, expression_value(actual callee) and the original
Apply checking occurrence slot0 (`:159–176`). Root registration does not replace
the callee receiver. If an Apply root already denotes that Expression Value,
interning reuses it. The source graph seals only after collection
(`lib.rs:1463`); definition SCC partition does not substitute for this Value
SCC relation. G2's exact, disjoint root/local/parameter/binder identities
instantiate the reachability argument in §7, including the absence of any
fabricated expression namespace return edge into an old definition.

The formerly definition-only reached source fields in §3 are now genuinely
lifted. FormalRegistrationInput, FormalNameInput and ApplySourceInput retain
SourceRootId (`candidate_call.rs:20–38`); source/root scopes have an honest
ModuleExpression case (`:421–435`). Their observers retrieve local_source_for
that owner, validate exact parameters/children/occurrences/cause and native
ports, and compare annotation ownership without projecting a definition
(`:202–217,438–490,534–606`). Definition-only prototype queries remain partial;
they do not run as the new general source-call owner.

`AnnotationScope::for_source` preserves Definition for definitions and Source
for an expression (`candidate_effect.rs:41–46`). Source root, local, formal,
Catch-arm and nested expression scopes are selected from actual retained
source scopes in the planner (`candidate_source.rs:580–607,1061–1069`).
SignatureContext::owner, View.owner, LocalWeight.owner and EmptyAttachmentSet
now use SourceRootId (`candidate_effect.rs:163–179`;
`candidate_context.rs:115–155`). Signature generation copies that same owner
into views (`candidate_effect.rs:1582,1604,1669`), source_weight copies it into
the actual weight (`candidate_context.rs:2401–2422`), and negative-empty bundle
construction retains it with the original lexical scope/position
(`candidate_effect.rs:1397–1427`). There is no definition-projection refusal in
these actual constructor paths.

The existing payload-view consumer checks owner, position, allowed members,
weight boundary and weight/view links (`candidate_context.rs:1626–1632`),
and retained evidence also checks weight/view owner equality (`:1143–1152`).
Effect-view copying validates that pair, clones the same source owner/position,
allowed operands and operation provenance, and creates the new view/weight
through that generalized constructor (`candidate_effect.rs:898–933`). FreshUse
uses one shared view remap for operands and context-backed views and preserves
bundle set payloads (`candidate_scheme.rs:1151–1225`). Thus generic copying
does not drop the newly admitted owner variant or rebrand it as a definition.
Resolved effect members and OperationOrigin declarations remain their original
declaration identities; expression provenance never becomes a SourceEffectId.

The definition-use observation records also retain the honest source-root
variant (`shadow_apply.rs:775–787`). Its definition-only export/context joins
explicitly return mismatch/None for expressions (`:685,866`); that is absence
of an expression export, not missing provenance or a second source namespace.

### 10.6 Conclusion, frozen hashes and handoff

These actual owners instantiate the original construction and its decisive
level/copy, authentic-use, publication and Value-association invariants for
every constructor case in the original statement. The earlier ownership and
pre-SCC-availability implementation seams are discharged by the cited paths.
No new source restriction, fake definition or independent Name solver is
needed. This is a constructive correspondence claim awaiting fresh independent
proof review; it is not full native source-packet interpretation, source
soundness/principality, whole-program coverage or runtime G4 closure.

All ten solver hashes below and all six HIR hashes listed in the consumed G2
note were checked against the actual frozen files during this bridge. The G2
note itself remains byte-identical to its stated producer hash.

Actual frozen solver SHA-256:

| `crates/yu-solver/src/` file | SHA-256 |
| --- | --- |
| `lib.rs` | `199963ac9cd13eebca44c4881b859eeb1f801259cc944bf1d5a57df78dc0c070` |
| `scc.rs` | `8f3709ec9d52dc79767b6822eb4f671118a3f83814d2e9a9c748dfeac51e1f72` |
| `candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `candidate_value_graph.rs` | `d08f6c5fb9ae4c5f005b6cb40aa3462f4f58b350cd6842b76a15d2dfdb520bec` |
| `candidate_call.rs` | `cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1` |
| `candidate_effect.rs` | `a330100b418f14be1c8f600c62970efdb4859818b603190846796de39fa8cef2` |
| `candidate_context.rs` | `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6` |
| `candidate_scheme.rs` | `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e` |
| `shadow_apply.rs` | `357b274d0de509931bda3015a99b1a1cf2ac86d75a45d230d62ab456c56740ba` |
| `candidate_receiver.rs` | `620b09011ec4dc4bfa71998e2b6fc1498b9299b3056662fdaa80b17376ba23c3` |

Primary reports production compiler/spec reviews CLEAN and G2 focused checks
default5/shadow6 PASS; those reports are correspondence evidence, not premises
for the constructor induction. Pending G3 fixture-mode/recovery-coverage repairs
are separate verification work and are not assumed complete here.

This bounded append used static rg/sed and hash reads only. No tests, builds,
probes, network, Git mutation, delegation or compiler edits. Sole changed path
remains this note. Budget: 25-minute allocation, zero heavy processes/measured
samples, exact elapsed/CPU/RAM uninstrumented. Normal Sol/high requested;
observed runtime metadata unavailable. Freeze before independent review; no
further writes are authorized after handoff.

Commit packet: append to
`notes/theory/2026-10-16-module-expression-receiver-construction.md`; original
baseline `1a64937f1`, actual dependencies above plus CLEAN G2 correspondence.
Proposed checkpoint:
`research: bridge expression receiver construction to actual G3 owners`.
Shared-record proposal for the primary: consume this actual correspondence
after fresh review together with the focused verification repairs; retain G4,
default cutover and the original native semantic parents OPEN. No shared record
was edited.

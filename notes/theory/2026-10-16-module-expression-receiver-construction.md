# Module expression receivers: constructive level and use-routing prerequisite

Date: 2026-10-16
Status: algorithm-level constructive derivation; implementation correspondence
OPEN after independent review of this construction. G3 remains OPEN.
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

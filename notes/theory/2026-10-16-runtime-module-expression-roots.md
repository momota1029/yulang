# Mixed module roots: authentic expression ownership and scheduling

Status: constructive source/transition derivation and implementation handoff;
independent source/transition review CLEAN. G4 actual-source correspondence remains OPEN until
the G2 authentic carriers and concrete runtime delta are supplied and reviewed.
Governing approval: module-expression-source-owner, Authoritative, answer bundle
`f40e4235d`; no new source semantics or materialization law selected here.
Dispatch baseline: `1a64937f1` (runtime unchanged from `05ebaf2ce`).
Exclusive lease: this new note only; no production edits, probes or delegation.

Independent review: compiler-referee `runtime_semantic_review` returned CLEAN
at producer SHA-256
`67f0c87f53c0db0936fd291b1546bafa3f3d00257efd1afc0e84bf1e3a8ec7cf`.
The accepted result is the source/transition handoff, including dependency-demand
ordering and the root-cursor/internal-capture invariant. Actual G2/G4 code joins
and full-runtime/source-domain correspondence remain OPEN.

## 1. Original claim, quantifiers and unresolved boundaries

Fix an authentic immutable HIR module, its original ordered items/occurrences,
all original binding DefIds and definition roots, direct-expression roots, source
interfaces and one joint assignment xi=(nu,K,D). ExpressionRootId is constructed
only by the actual direct-root HIR owner; SourceRootId is the honest disjoint sum
Definition(DefinitionRootId) | Expression(ExpressionRootId). Fix an existing
selected definition d. Expressions are not selected definitions, exported
schemes, synthetic bindings, Lambdas or members of the definition namespace.

Required G4 conclusion: construct the complete mixed demand list in original
item order; run its computed-definition demands and **every** direct expression;
discard each expression's normal result without a global cache publication;
then observe/materialize d exactly as the existing selected-definition route.
Preserve every finite ordinary/request/Catch/raw-Resume prefix on implemented
paths, original source/value/view/control identities and dynamic executable
ownership. No skipped unsupported/recovered expression may masquerade as a
completed root. No resource/unavailable outcome is identified with a source
result, source rejection or divergence.

The unchanged ordinary type/operation/OpCompat/typed-view premises are those
of the existing reviewed local runtime theorems. G2 carrier authenticity and G3
inference/level/FreshUse/copy correspondence are separate owners, not supplied
by this runtime derivation. Cache-bearing GlobalRead/definition-Root capture
continues to report explicit provisional unavailability; its two materialization
laws remain unanswered and are not inferred from this approval. General
visibility, higher-order/symbolic transport, full raw-Resume/source completeness,
native inference and production parents remain OPEN.

## 2. Frozen actual source evidence and present missing constructors

HIR reads use `git show 1a64937f1`, not the concurrently edited HIR. That baseline
already retains HirItem::Expression(ResolvedExpr), with its original artifact-
branded HirOccurrenceId, and forms items by iterating source plans in order.
Direct-root expressions do not allocate DefinitionRootId or consume DefId
ordinals. Its ordinary LocalSource/carrier tables are still keyed only by
DefinitionRootId; the new G2 tagged ownership/carrier constructors are absent
there. This is precisely the approved extension, not a reason to forge a root.

The inspected stable runtime is still binding-only:

- `program::from_hir` accepts actual Bindings and exact Act placeholders, rejects
  other items, and appends only definition bodies to its code/definition tables.
- `SourceSite` stores definition/occurrence/range. Annotation/formal/local/Catch
  owner comparisons currently use that definition-only source owner.
- `execution_roots()` scans definitions in retained order, follows transparent
  Forward/empty Block, and takes the existing Apply/If/Catch/nonempty-Block
  computed-demand subsequence. It returns `Vec<DefId>`, with no expression item.
- `Machine::begin_root` schedules a definition index, creates its pending cache
  marker and `Frame::Root {cell,next}`, then writes its actual normal result
  to that cell before advancing. Its final phase observes/materializes d.
- The actual consumer `lib::execute` obtains definition_named, execution_roots,
  and passes that exact complete vector to start. Arbitrary reordered caller
  vectors are not the source-order theorem's premise.

Thus the current runtime cannot implement an actual direct-expression demand.
The missing operations below are concrete construction/consumer deltas, not
claims that changed types or future implementations already satisfy them.

## 3. Minimal transition construction derived from the approved law

Retain the existing definition array, DefId-to-index map and definition cells.
Add an authenticated expression record with original ExpressionRootId and
its checked code label; it has **no** DefId/global cell. Retain a source-item
schedule from the original HIR item traversal, rather than reconstructing order
from separate definition and expression collections.

```text
ExecutionRoot = Definition(existing index)
              | Expression(original ExpressionRootId, checked Label)
```

Fold original HIR items left to right: a computed Binding contributes its
ordinary Definition demand using the existing source fetch classifier; every
supported direct Expression contributes its Expression demand, even an integer,
Name, bare value or returned closure. An exact Act placeholder contributes no
executable demand. Unsupported/recovered/unavailable source follows its actual
carrier outcome and existing unavailable boundary; it is never silently omitted.
Noncomputed definitions retain their original demand-on-read behavior.

SourceSite now retains SourceRootId, occurrence and range. Compile each actual
supported carrier once into the same code arena through its owner-checked child
indices. G2 must supply authenticated direct-root carrier access; runtime cannot
construct ExpressionRootId from a child occurrence, ordinal or foreign artifact.
Definition-only accessors remain restricted/partial. No new expression result
scheme or second source Name-instantiation algorithm is introduced.

Use a separate cache-free completion frame, schematically:

```text
ExpressionReturn { original root, next cursor }
```

For mixed list R and cursor j, the source-derived machine handshake is:

```text
schedule(j), R[j]=Definition(i), cell[i] complete:
    schedule(j+1)                         // existing cache skip
schedule(j), R[j]=Definition(i), cell[i] unmaterialized:
    push Root(cell[i],j+1); start original definition in environment 0
schedule(j), R[j]=Expression(e,label):
    push ExpressionReturn(e,j+1); evaluate label in environment 0
Return(v) at ExpressionReturn(e,j+1):
    discard this result; schedule(j+1)    // no cell/marker/value publication
schedule(end):
    existing observe/materialize(selected definition d)
```

These root entries and completion suffixes execute in ModuleRun. Do not create
an invocation to run an expression, and do not forcibly overwrite an inconsistent
current owner: normal frame/owner correspondence must establish ModuleRun at
each reached scheduling boundary. Genuine Calls still mint their actual
Invocation; Force inherits the then-current executable configuration.

The existing definition Root/GlobalRead protocol is unchanged. In particular,
ExpressionReturn must not reuse Root with a sentinel/selected/phantom cell, nor
add an initialization marker. `abandon_suffix` continues to release only the
actual cache-bearing owner frames, never the cache-free expression completion.

## 4. Mixed source-order and completion invariant

Let R be the left-to-right list just constructed. At each root boundary j,
every scheduled slot less than j has either completed its required demand or
legitimately skipped an already materialized definition. No slot at or after j
has been scheduled by the root cursor. During a root's pending evaluation,
its unique completion frame holds its exact next cursor; the later demand
suffix is inert until that root normally completes.

Dependency materialization is distinct: a Name in an earlier expression may
demand a **later** definition before that definition's scheduled slot. This is
the existing GetDefinition law, not a violation of root order. Its later
Definition slot then observes the completed cache and skips. The theorem is
about ordered scheduled demands, not timestamp-sorting all initializer calls.

Proof by cursor/transition induction:

1. Original HIR source planning and item emission preserve order; filtering
   only noncomputed definitions/true declaration placeholders preserves relative
   order and includes every expression. G2 authentic carrier access preserves
   each original item/occurrence rather than manufacturing a replacement.
2. Definition cache skips and normal materialization use the existing reviewed
   root/global invariant. Their only root advancement is the retained next cursor.
3. Expression entry schedules its exact code once and records j+1 without any
   global publication. On normal completion, discard and advance proves the
   next-boundary invariant. A returned closure is discarded without invocation;
   a Name root fetches its source value without inventing a call. The expression
   demands themselves are unconditional, including Value-shaped roots.
4. Requests, unavailable exits and resource pauses do not return through that
   completion frame. They therefore cannot prematurely advance j or publish an
   expression result. Requests retain their original pending suffix/event.
5. At exhaustion the old selected-definition phase runs. A cached d returns its
   old actual value; an uncached d materializes through its ordinary definition
   write owner. The last expression is not a module output or the CLI result.

Consequently every finite normally completed run visits the complete mixed
source list in order with the allowed dependency skips/materializations, then
returns the selected definition's value. Prefixes preserve pending work rather
than pretending the remainder executed. No termination claim is required.

## 5. Provenance, executable owner and capture/Resume boundary

### Ordinary Calls, Force and Catch

SourceRootId is static provenance only. Code of an expression can be the source
of a Lambda, delayed argument, operation request or handler, but its original
ExpressionRootId neither equals nor chooses a dynamic Invocation/ModuleRun.
Reuse the reviewed executable-owner transitions: closure/native Call allocates
a fresh real Invocation; Value entry forces its argument inside it; retained
Comp entry is inert; Force runs captured code under Cnow; native return ends
its owner before the declared result consumer. A Catch snapshots the actual
current installer, not the code author's source root. Return/unwind removes
only its exact dynamic owner/handler. Views preserve original receiver identities
independently of both static source provenance and current executable owner.

The new source tag changes none of these control constructors. Source/parameter/
local/Catch owner checks must use their honest tagged source root, including
expression-owned local Lambdas and captures. They cannot call a definition-only
accessor on an expression and fill the gap with a referenced definition. A
handler inside an invoked relay is still relay's actual Invocation; a direct
root Catch with no Invoke is owned by ModuleRun.

### Root completion is outside internal raw capture

For fresh module execution, strengthen the frame invariant: the active module
root completion (definition Root or ExpressionReturn) lies below every handler
installed while evaluating that root. No handler from a previous root survives
normal root completion: its ordinary delimiter must finish/exit before the
root's Return reaches its completion frame. A returned latent closure or saved
raw continuation does not leave its maker's Catch active.

Induction on ordinary evaluation preserves this ordering: code pushes handlers,
calls and View frames above the existing root completion. Forwarded handlers
and owner/view wrappers installed during raw Resume are also above that live
outer frame. A capture folds only the already popped suffix **strictly inside**
the reached selected handler; hence that suffix never contains the module root
completion. The still-containing owner wrapper records owner attribution, not
the unexecuted stack below the capture bound. This is exactly the reviewed raw
template rule; no full-stack/scheduler capture is permitted.

Each invocation of a captured raw continuation therefore returns once to its
current resumer. Repeated k calls can repeat their captured body suffix, but
cannot schedule the next module root on each call. After those calls/arm finish,
the original root body finally returns to its one ExpressionReturn and advances
the module cursor once. If the root emits an unhandled event, its opaque saved
suffix can retain the root completion, but there is currently no public API
executing that opaque handle; no source module-return rule is inferred for a
future external resumer.

ModuleRun remains the ambient live owner when a raw template records it. A raw
entry from inside another invocation may borrow ModuleRun, then restores the
resumer's previous executable owner at its matching OwnerReturn. An expired
saved Invocation instead enters the source-prescribed fresh executable span;
it does not replay entry or rename old boundary receivers. These existing
owned/borrowed rules keep current expression code and its root cursor separate.

### Flat templates and cache-bearing frames are different obligations

The current `TemplateNode::Bind` stores an ordinary Frame by value; nested
continuations inside frames contain only arena TemplateHandles. A cache-free
ExpressionReturn can be represented without adding recursive ownership. This
storage fact alone does **not** certify arbitrary Resume of its scheduler:
`schedule(end)` observes a selected definition and may stop the machine, rather
than returning an invented module value to a resumer. The proven internal-capture
boundary above is what makes that case unreachable in this G4 extension.

Keep the existing explicit capture rejection of GlobalRead/definition Root.
Those frames own pending global publication, unlike ExpressionReturn; approval
does not answer their suspended-write/multi-shot laws. New expressions may
themselves demand definitions under a handler, so cache-bearing capture can
still reach that existing provisional boundary. Do not close it or broaden it
to all expression/Resume source cases. A future external module-capture API
would need its own source completion law; none is added here.

## 6. Whole-program certificate extension

The reviewed closed-primitive proof is about the complete constructed execution
universe, not a definition-only list. Its actual classifier currently seeds
Ground traversal from all definitions, and checks owner equality using
definition-only SourceSite/local/Catch IDs.

Required delta: seed that same traversal from **every actual expression body**
as well as all definitions, including unused/unselected code and all arms;
retain the orphan-state check. Compare local/Catch ownership to SourceRootId,
with full artifact/authentic-root equality. Internal ModuleDef Names still refer
only to the unchanged definition map; expression roots do not become callable
aliases, module definitions or global cells. Preserve every existing primitive
declaration/role, cycle, Lambda and continuation-pattern check.

The source proof then extends by an additional initial-root case: a closed
primitive expression begins in the same fresh ModuleRun/closed environment;
its constructors and dependencies satisfy the reviewed no-profile induction;
discarding its ground result creates no profile or imported context. Root
sequencing shares only the already certified internal globals and immutable
program. Thus each actual certified event still has !Protected, including a
direct expression Catch. Source-supported expressions outside the classifier's
closed grammar simply withhold this conservative certificate; truly unavailable
source carriers still follow §3's explicit unavailable boundary. The existing positive-Grant route and
ordinary source admission remain untouched. No syntax-local certificate reuse
inside arbitrary received views is justified.

## 7. Exact implementation seams and cost

| Owning responsibility | Required output/consumer |
| --- | --- |
| G2 HIR/carrier | Actual ExpressionRootId/SourceRootId, original item order, owner-checked supported direct-root carriers; separate unsupported/recovered/availability outcomes; preserved original definition identities. |
| program SourceSite/owner consumers | Retain honest tagged source root; generalize schema/local/parameter/Catch ownership without converting expressions into definitions. |
| from_hir/code arena | Compile actual expression carriers once alongside definitions; retain original mixed source-item positions and authentic expression/code joins. |
| execution_roots/start | Emit/validate tagged mixed demands in original order, all expressions included; preserve source computed-binding classification and the actual full-vector CLI consumer. Validate foreign/cross-artifact expression handles. |
| Machine scheduler/frame completion | Separate cache-free ExpressionReturn; evaluate in environment 0 under established ModuleRun; discard actual result and advance once; no cache/marker allocation for expressions. |
| Existing Name/global/selected routes | Definition map/cell indexes and --run definition selection unchanged; demand-on-read and end-of-plan selected observation remain their original consumers. |
| Capture/Resume/abandonment | Retain exact inside-handler capture bound and flat-handle storage; do not append scheduler suffix into templates or change the Root/GlobalRead cache-bearing guard. |
| Closed primitive classifier | All expression roots seeded and source owners tagged; no omitted code or uncertified global negative-visibility decision. |

For source/code size N, root count R and original references/edges E, retain
one expression/root record per relevant item and ordinary one code record per
actual retained node. Compilation/root-list construction and whole-program
classification require O(N+E+R) structural work/storage with explicit original
ID hash/equality cost. The scheduler processes each root slot once in O(R)
total cursor work, plus existing actual evaluation/materialization. No source
scan is needed at a transition. Raw capture continues to allocate flat nodes
for its actual saved suffix; no scheduler cloning or historical-owner scan is
introduced. These are required structural bounds, not measured performance
or proof that an unprovided implementation attains them.

## 8. Discriminating falsifiers and review obligations

- **Mixed order:** interleave computed definitions, direct Name/application/
  integer roots and later computed definitions. The emitted plan must match
  the original item order, rather than concatenate kind-specific vectors.
- **Forward dependency:** an early Name expression demands a later definition.
  Its later scheduled Definition slot must skip the completed cache; expression
  result is still discarded. This distinguishes root order from illegal repeat
  materialization or an incorrect timestamp-sorting invariant.
- **No expression publication:** `99; my selected = 7` followed by --run selected
  must observe 7; the integer root has no global cell/DefId/scheme. Discarding a
  root closure must not invoke it.
- **Owner:** a direct root Catch is ModuleRun-owned; a root invoking an existing
  relay has a relay Invocation-owned Catch. Source ExpressionRootId is neither.
- **Capture/cursor:** use explicit permitted `relay(thunk:[io]int)` whose io arm
  binds k and calls it twice, then two direct roots `relay(io::tick 7)` and
  `relay(io::tick 9)`. Each raw call returns to its resumer; the second root may
  not execute during each k invocation or be skipped by premature Completed.
  This is a concrete source-compatible control falsifier, not a test run.
- **Classifier:** a direct primitive Catch expression alongside primitive
  definitions must be included in the same whole-program certificate. An
  expression Lambda/bound continuation must invalidate that certificate even
  if the selected definition alone is primitive.
- **Authenticity/recovery:** reject a foreign/child root handle as a root;
  unsupplied/unsupported/recovered expression carrier cannot be silently skipped
  and followed by a purported Completed selected value.

These are exact source/correspondence checks for primary-owned implementation
verification; no test, build or probe was run by this leaf. G4 actual closure
requires review of the implemented constructors/consumer at frozen hashes,
not merely passing these examples or using the proposed type names.

## 9. Freeze and commit packet

Stable runtime dependencies under `tools/inference-playground/src/runtime/`:

```text
program.rs 9bb9150a161fc0bed20fb4559649cf08719e570b0662558e9efadcf775edcc55
machine.rs 25e61fa3fd06bdf9da09750f37fcac321da9d28fbb27e650fd3cf37a604bd973
primitive.rs ad0cfd8a8b7d7ad2a83a363668fbaf2bbf19764dceaf0f093978c342c1559ebb
mod.rs 8707ad039dc402f2ff9e3ce243594e4524c838cfbfa5e6f4c877c51cd746f63e
continuation.rs c1d71046efec8dcc6393b81a85c686aef82a94edc1f5e43b9cb90c4efb49c86d
receiving.rs 3d1ce66e6b68fd11463724431098216e0270d55cc5d6406b7aeb15ea802c8229
```

Read dependency SHA-256:

```text
module-expression-source-owner.md 9a48f9ce4bee6e533cb0198d4112803dff927df71f5bca6bec084ced204dcd66
hir-direct-root-expression-slice.md e2ca3943817e70de5b51bf432d696e3b3fdf90d85539e92ba429c6102691237b
playground-ordinary-runtime-simulation.md 16dcc7252c966a6d0f317ed9625cf9f5c101e4bada5f9f00d0788fe4ebe28a8b
runtime-execution-owner-correspondence.md 8a7bbd5cd69f6a8c5ae87b2cf737a8e5fc45028ab416bfeea913c5cb490eb9a3
runtime-resume-template-correspondence.md db73872c8395a27f2bdf72d08228c69209c73fc98ef6bf614888dd5dc8ad1b4d
runtime-primitive-event-visibility.md 7b27f8cf1d8024e249cc7d8a433c77438e3f59e5543cfc46a96a1af278eb3f56
```

HIR baseline is the immutable
`1a64937f127082704fc8adf998d1ebaaed4f4f28` blob set; live HIR edits were not
read. Its module.rs SHA-256 is
`c32e3e61df7a4ce4cf4e2b29c1728f14083bd3821dcba2eb56b1f60a81b9fce5`;
local_source.rs is
`13c134afb7f85996c2f12fd27fbb78ab640878611287ca4952c10fd48cfd4c81`.
The primary later leased compatibility edits to primitive.rs/receiving.rs;
their final proof inputs were revalidated with `git show 1a64937f1`, not those
live edits. Program/machine/mod/continuation remained byte-identical on final
rehash. The actual full-root CLI consumer lib.rs hash is
`bace98ef2f11c9bb638b4f1f7536178c668ca8b0448fb0276986fbf0772f524b`.
Read-start HEAD was `574026a204445120988dbccdf9bd81d202435054`.
Checks: bounded static authority/source/consumer reads, read-only git show,
dependency hashes and final whitespace/hash check. No tests/builds/probes/
network/Git mutation/other writes/delegation. One <=25-minute leaf pass; zero
heavy processes/measurement samples. Requested Sol/high; actual runtime
model/effort unknown. Independent review and actual implementation bridge are
pending; the producer does not certify its own result.

Commit packet: sole lease
`notes/theory/2026-10-16-runtime-module-expression-roots.md`; original baseline
and frozen dependencies above; research-only proposed-constructor derivation.
Suggested checkpoint: `research: derive mixed module root runtime invariants`.
Shared-record delta: retain G4 OPEN at authentic expression compilation/mixed
plan/ExpressionReturn/classifier consumers; use this finite handoff for the
approved implementation without waiting for the separate cache-bearing Resume
decision. Next action: implement these exact owners, freeze the code/G2 joins,
then construct/review their actual-source correspondence; do not claim the
present binding-only runtime already implements mixed roots.

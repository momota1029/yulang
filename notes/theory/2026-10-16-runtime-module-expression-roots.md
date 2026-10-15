# Mixed module roots: authentic expression ownership and scheduling

Status: original constructive transition derivation and §10 actual runtime
correspondence independently reviewed CLEAN within the explicit component
premises. G2 formation is separately established. Whole typed-source root and
definition-materialization adequacy, and broader runtime/inference parents, OPEN.
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

Actual-bridge review: `runtime_semantic_review` returned CLEAN at producer
SHA-256 `965b928570876f1e343abad99ba4e565edd3c875cdc6e487f20561682b34fd86`.
Following the consumed user correction in bundle `1e62dfdc3`, the same reviewer
accepted the narrow §4/§10.4 source-premise qualification at
`f36e667265d7aaead29314bf27ddf1aad4a5488ab005638a850d70ad3734e352`.
It preserves the original structural/control quantifiers and leaves whole
typed GetDefinition/root adequacy OPEN at its preexisting source bridge.

Final verification metadata: machine.rs changed only in its new cfg(test)
helper to use existing opt-in lowering for an Act/annotated-header fixture;
its final hash is
`e30bb19c54b1a4ee07f3b1d2f0a5e88e57f2226fd055071a6d1ca5f1bdfd5e3a`.
The integration-test hash is
`6e62ed611c81e847bec4a33238da55b7e5ee6851116967f182b3ffe2d1c2cf40`.
These precleared fixture changes preserve all source/outcome assertions except
moving the bare-`@` refusal to its actual syntax entrypoint; no production
premise changed. The primary's full package check passes all 103 tests.
Section 10.9 retains the producer's earlier evidence hashes.

Sections 1–9 retain the preimplementation snapshot and its missing-operation
inventory. Section 10 consumes the later concrete runtime delta; those earlier
descriptions of binding-only code do not describe the new frozen implementation.

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

Dependency materialization is a distinct component premise. The actual empty-
global Name machine path can enter a later definition body before its scheduled
slot, after which that slot skips a completed cache. This structural cursor fact
and the pure forward-reference fixture do not prove that an effectful initializer
may execute or be handled at the reference site. The consumed user correction
in bundle `1e62dfdc3` explicitly distinguishes the published value from its
initialization effect; the earlier `pending` example is not a valid source
reachability witness. G4 preserves ordered scheduled demands relative to the
existing definition-materialization component premises. Whole typed root/
materialization semantic adequacy remains OPEN at the unqualified GetDefinition
source bridge in ordinary-runtime-simulation §5 (lines 538–549); no initialization
publication, forwarding, failure or capture law is selected here.

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

## 10. Actual frozen G4 constructor and consumer correspondence

### 10.1 Statement and exact source dependency

The primary supplied the six implementation hashes in §10.9; every one matched
the first read. Observed read-start HEAD was
`acf9422aecd1117886866ab881780bfeb55f5846`. Keep all original source scopes,
identities, assignment xi and conclusions of §1. For authentic current HIR with
its supported G2 carrier outcomes, let P=from_hir succeed, R=P.execution_roots()
and let d be its existing selected definition. Prove actual start(d,R) and every
finite implemented execution prefix realize §§3–6's mixed plan, cache-free
expression completion, owner/control and certificate invariants; every actual
Completed observation remains d's value after the complete mixed schedule.

The original ordinary/request/selected-arm/typed-view/raw-Resume premises remain
those of the reviewed component theorems. This proof does not assume a future
runtime transition. It consumes actual HIR API/identity checks below, while
the full source admission/formation/order/binding-preservation theorem is the
separately owned G2 result now accepted independently CLEAN by the primary at
producer SHA-256 `57ba5d19388ad30fce91fb3368bd6e07032336c4c3dd62175b52df6e7211f085`.
Its exact source conclusions are applied below rather than left assumed. G3 is
actively changing and is not read or used as inference-adequacy evidence.

### 10.2 Actual root authentication, carrier compilation and provenance

At each original HirItem, `from_hir` constructs the source owner by exact case:
Binding uses its original DefinitionRootId; Expression calls
`hir.expression_root(expression.occurrence())` and retains the returned original
ExpressionRootId. Failure is explicit InvalidSourceReference/MissingSource,
not a fabricated binding or skipped expression. The actual HIR constructor
mints ExpressionRootId only under RootPlanKind::DirectExpression, from that
plan's freshly branded original occurrence, and keeps it in the expression-root
map. The API rejects foreign occurrences and map lookup cannot turn a child
occurrence into a direct root. SourceRootId's disjoint tags preserve the
old definition identity rather than allocate a replacement DefId.

For either tagged owner, runtime calls `local_source_for`. Its actual HIR path
checks owns_source_root and returns only Supported carrier contents. Unsupported
is None; an expression has no definition-only fallback. Consequently any
unsupplied/unsupported actual expression fails runtime construction, including
genuine recovered expression carriers; it does not vanish from the schedule.
The existing exact Act placeholder check is the sole skipped item case.

The code-label closure validates each LocalSourceIndex through
`source.expression(index)` before using offset+ordinal. That accessor checks
the exact tagged owner, then bounds. All code is emitted once for the actual
carrier arena and all SourceSites carry the same actual source_root plus their
original occurrence/range. Child/cross-artifact ownership is never inferred
from ordinal equality. The recursive-local walk, original parameter role table,
source-resolved Name/Binder operands and all ordinary instruction constructors
remain their existing algorithms, now parameterized by the honest source tag.

The runtime uses full `SourceRootId` equality for expression-owned schemas:
`RootCompSchema::from_parameter` requires annotation.owner=lambda.source_root
and formal.id.source_root() equal to it, retaining the original annotation,
formal and row. The later Grant check uses the same owner equality. It does
not project an expression into a definition or silently drop its applicable
Comp schema. Environment Binder lookup remains equality on original parameter/
local/Catch IDs, so the existing lookup/closure-capture proof is parametric in
this generalized owner type. G2 supplies the original scoped ID constructors;
runtime retains them without another spelling-based resolution step.

Apply the independently accepted G2 theorem's five original conclusions to
these exact matching HIR hashes: (1) every and only actual direct Expression
has its private authentic original-item root, discharging root-map provenance;
(2) ordinary projection and old binding IDs/equalities are preserved by the
injective definition-owner embedding, discharging compatibility rather than
assuming numeric Hash identity; (3) each binding/expression has one source-
ordered outcome and supported expressions retain their original body occurrence,
discharging complete inventory/body-label joins; (4) generalized scope/owner/
reference construction is exact, discharging the runtime Binder/source-owner
premise; (5) refused/recovered formation publishes no partial carrier/cursor,
while genuine failures remain availability errors, discharging staged refusal
and atomic compilation inputs. Its opt-in single-ownership conclusion supplies
the existing binding adapter case as well. No runtime or G3 claim is read into
that HIR theorem; these are its actual source outputs consumed here.

### 10.3 Mixed plan and public-to-internal validation

Still inside the single left-to-right HIR item loop, after compiling its body:

- Binding appends its unchanged DefId/body to definitions and its DefId/index
  map. The same former fetch classifier follows Forward/empty Block and marks
  Apply/If/Catch/nonempty Block. Only a computed definition adds a demand.
- Expression inserts its exact original root/body join into expression_roots
  and unconditionally appends an Expression demand, including literal/Name/
  Lambda-valued expressions. No definition/cell record is appended for it.
- The immutable program is published only after the entire item loop and
  whole-program classification. A failed later carrier cannot expose a
  supposedly completed prefix program.

Public `ExecutionRoot::Definition(DefId)` is the compatibility adapter; it is
not the internal cache representation. `start` resolves it through this
program's unchanged definition_indices to ScheduledRoot::Definition(index),
rejecting missing or duplicate definition indices. Thus every cache index is
an actual definition's index, and definitions retain their old binding-only
subsequence/order regardless of expression code interleaving.

Public ExpressionExecutionRoot contains root and code fields private to the
runtime implementation, with only a public read-only source_root accessor.
`start` looks up that original root in this program's expression map, requires
the exact stored code ordinal and `hir.owns_expression_root(root)`, rejects
duplicates, then constructs ScheduledRoot::Expression {root,checked Label}.
An identical-looking foreign artifact, a mismatched private code join or a
child root cannot enter through this path. The G2 uniqueness of actual direct
root occurrences makes the construction map injective; runtime never makes
an expression alias by reusing a definition index.

`execution_roots()` clones the actual source_schedule, so its list is exactly
the HIR item-order fold of §4. It does not iterate the expression HashMap or
concatenate separate kind vectors. The actual `lib::execute` still obtains
definition_named, then this exact execution_roots vector and passes it to start.
That closes the full-vector source-order consumer premise. Public start also
allows validated custom subsets/order as before; this theorem does not falsely
claim that their identity checks impose source order. Its fixed R is the actual
constructor output, as in the original ordinary runtime theorem.

### 10.4 Actual scheduler and expression completion

Machine allocates global cells/globals from definitions only and stores the
validated internal mixed plan. Initial owner is ModuleRun, with empty owner/
handler/template/evidence history and environment 0. `begin_root` checks
current_owner=ModuleRun rather than overwriting a conflicting owner.

Its loop consumes one ScheduledRoot slot and increments the cursor. Definition
uses the old completed-cache skip or marker+Root(cell,next) path. Expression
pushes `Frame::ExpressionReturn {root,next}` and evaluates its checked code in
environment 0. It allocates no initialization marker/cell and mints no Invoke.
The return branch validates the retained root still belongs to the immutable
program, then calls begin_root(next), without publishing or reusing received.
Thus even a returned closure/carrier is discarded rather than invoked or stored
as a module result. Original global values materialized by actual Names remain
the existing shared cache, not an expression result cache.

Apply §4's structural cursor induction to these actual branches: a root starts
only at its slot, and the next root starts only after its completion branch.
Definitions successfully materialized by the actual Name path are skipped at
their later scheduled slot; expression slots are never cache-skipped. Relating
that on-read materialization to a valid typed source is the existing component
premise, not a new G4 conclusion about initialization-effect ownership. In
particular bundle `1e62dfdc3` forbids using this runtime path or the pure forward
fixture as proof of the withdrawn effectful `pending` scenario. On Request the completion remains
pending or is saved during propagation; on unavailable/pause it cannot run.
At exhaustion begin_root has precisely the old selected-definition observation/
materialization branches using the existing selected index. It never reads the
last expression result. This proves ordered demand completeness and discarded
expression return for every actual completed run under the fixed R, relative
to the source/control and definition-materialization component premises in
§10.1/§4. It does not close the ordinary runtime's whole typed GetDefinition/
root adequacy, establish valid cache-bearing capture, or prove its unreachability.

### 10.5 Actual dynamic owner and reusable control paths

SourceSite now holds source_root; the dynamic ExecutionOwner sum and owner
transition rules are unchanged. `new_invocation` still receives original call/
provider sites and allocates a fresh Invocation, rather than deriving an owner
from either site's static root tag. Value entry and Delay execute under that
actual current configuration; native result consumption follows its native
receiver return. Catch snapshots current_owner; dispatch validates that exact
installer's current/live occurrence. The receiving engine retains original
boundary.receiver separately from source provenance and current owner.

Therefore a direct expression Catch belongs to ModuleRun and a Catch in an
invoked expression-owned relay belongs to that relay's actual Invocation.
Captured lexical code keeps its source root but Force does not restore a maker
owner. Returning each complete root restores ModuleRun through the existing
matching owner delimiters before the next begin_root check. These are applications
of the reviewed owner/ordinary/raw transition proofs to unchanged actual owner
constructors; no additional source-root-dependent owner case was inserted.

The new expression scheduler frame is below every handler installed during its
root. The constructors only push ordinary/Call/Catch/View frames above it.
Actual capture_template folds only request.suffix, which consists of frames
already popped strictly inside the reached selected Catch; it adds the saved
containing owner but no stack below that Catch. Hence §5's root-cursor exclusion
is preserved by these actual constructors. Existing templates initially contain
no scheduler frame; restoring/recapturing them cannot create one inductively.
When a saved continuation is invoked in a later root, its original code may
retain a prior ExpressionRootId, but its raw suffix has no prior root cursor.
Its OwnerReturn restores the current resumer; the live scheduler belongs to the
currently running root, not the code author's provenance.

Each raw call still uses fresh per-use control and one ResumeReturn. Multiple
k invocations can repeat only their captured inner suffix, returning to the
actual root arm before its final return advances the module cursor once.
The new Frame stores only root/cursor handles; TemplateNode::Bind and flat
TemplateHandle arena ownership retain the previous nonrecursive storage rule.
No new recursively owning scheduler/template pointer is introduced.

Actual capture still rejects GlobalRead/definition Root before publication.
ExpressionReturn is not a cache-bearing frame and is not added to that guard;
its inside-handler capture case is unreachable as just proved. If an unhandled
event crosses the expression completion, it is retained in the opaque saved
continuation. The runtime still exposes no public execution API for that opaque
handle. This is not a proof of an external scheduler-return/module-value rule.
Current cache-bearing Resume unavailability and the unanswered materialization
decision remain unchanged, including when an expression demands a definition
inside its Catch. No inconvenient source suffix is declared forbidden.

### 10.6 Actual whole-program negative certificate

`primitive::closed_primitive` now seeds Ground traversal from **all** definition
bodies and all values in program.expression_roots. The latter HashMap iteration
order is irrelevant to this predicate; it is not execution order. Its full code
prepass, all-arm traversal and orphan-state check remain. Local and Catch binder
ownership checks now compare source_root() to code.site.source_root, accepting
authentic expression-owned primitive bindings without inventing a definition.

All previous declaration/known-callee/role/cycle/Lambda/continuation checks are
retained, so accepting the expanded closed universe has exactly the additional
initial-expression case proved in §6. It cannot ignore a Lambda or raw binder
in an unselected expression/arm. `from_hir` runs this predicate after all roots
and code exist and before publishing the immutable program. Actual dispatch
still permits the negative branch only through this boolean, otherwise requiring
the original authenticated positive Grant. Live owner/handler, exact operation,
payload compatibility and original selected-arm OpCompat remain separate.

Thus direct primitive expression handlers obtain source !Protected under the
same closed initial context, while expression-owned higher-order/received
programs retain the positive route and original unknown-coverage limitations.
This changes neither source admission nor complete general negative visibility.

### 10.7 Coverage, test comparison and limits

The new runtime_module_expressions file checks mixed HIR item/root order,
forward Name materialization and discarded Value roots, closure discard,
ModuleRun primitive handling, expression-wide classifier exclusions, real
expression-owned relay/helper receivers, repeated permitted raw continuations,
request provenance/pending suffix, foreign/duplicate roots and unsupported
source. Private machine tests inspect zero expression cache/marker allocation,
mismatched root/code rejection and the absence of scheduler frames from actual
raw templates. These are focused discriminators of §§4–8's invariants, not
premises of their proofs, and were not executed by this leaf.

The original test snapshot's `@` case is not used as evidence of an admitted
recovered Expression. The primary cleared the existing admitted `f(@missing)`
source fixture; the final observed file includes that case as well as the
tuple and `@` cases. This proof uses the universal actual HirItem::Expression
-> checked local_source_for branch, whose None/error stops construction,
and the accepted G2 recovered-carrier theorem. No assertion is changed here,
no claim about the `@` case is needed, and no successful package run is claimed
by this leaf. Test-content changes do not alter the six frozen runtime files.

There is no missing runtime operation postulated in §§10.2–10.6. The actual
source dependency is discharged by the accepted G2 authenticity/formation/order/
binding-preservation theorem at the frozen HIR hashes, with the original shared
typing/interface hypotheses. Fresh actual G4 proof review must accept this
application and its runtime joins before the primary closes G4. G3/inference adequacy is not inferred from
runtime root scheduling. General visibility/Function/B, full source/Resume,
cache-bearing capture and production parents retain their original OPEN scopes.

Structural bounds match §7: one expression record/demand per actual item,
one code emission per carrier node, one mixed-plan slot visit, no per-step
source scan. Plan cloning/start validation cost O(R) structural work with ID
clone/hash/equality costs; definition/cache maps remain definition-only.
Classifier traversal is the reviewed expected-linear graph work with explicit
ID hashing/comparison costs. Actual expression frames add constant-sized root/
cursor references, not a cloned remainder or template chain. No timing or
worst-case hash claim is made.

### 10.8 Claim class and next action

Submitted result: actual frozen runtime-side G4 correspondence for the original
mixed-root statement under the named original source/type premises, consuming
the independently established G2 source outputs rather than a pending source
bridge. Every new runtime constructor/consumer is inspected and derived. It
is not a future implementation plan, an unconditional whole-source theorem or
producer-certified closure. Preserve the original source derivation/review and
independently review this actual delta at its exact input hashes.
No implementation or semantic change is requested by this result.

### 10.9 Final dependency/verification/commit packet

| Frozen actual runtime dependency | SHA-256 |
| --- | --- |
| program.rs | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` |
| machine.rs | `e5713fac40a2823168564d9f35ce824a1eb09f2fe3590a663ba626676422892b` |
| primitive.rs | `97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153` |
| receiving.rs | `5443c8ca55e58a37b6d003cf5b2985214d37776094f02637adfbe30200cc36bd` |
| continuation.rs | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| mod.rs | `64d208743793a03501a76f56bc2b511c50ed40cff3f789757a00b7d608fc846b` |
| tests/runtime_module_expressions.rs (final inspected, not run) | `5affadec63092d78ade24be22b53df60e381957c42e05a2d7767570531d2de53` |
| playground src/lib.rs (full-vector CLI) | `bace98ef2f11c9bb638b4f1f7536178c668ca8b0448fb0276986fbf0772f524b` |

Frozen G2 input hashes supplied by the primary and matched on read:

```text
yu-hir/src/module.rs 2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e
yu-hir/src/module/local_source.rs ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5
yu-hir/src/module/source_annotation.rs b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f
yu-hir/src/source_identity.rs aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2
yu-hir/src/lib.rs 5bdcb7c0df022da919cef5402c62dc1c7baf0700a4d06e526a608cbd7db21464
yu-hir/src/shadow.rs 2dffd7fd6542eed9fd3346e0672e76197c248be9c84334f341c4d612234b7ee9
```

Runtime paths are tools/inference-playground/src/runtime; HIR paths are under
crates/. Original authority/component-proof dependencies are those of §9.
Checks: all supplied runtime hashes first/final; G2 source hashes; bounded
actual constructor/consumer/API/test-content reads and whitespace check. Zero
tests/builds/probes/Git mutations/network/delegation or writes outside this note.
Requested normal Sol/high, observed runtime model/effort unknown; one <=20-minute
static pass, zero heavy processes or measurement samples. Fresh independent
G4 proof review remains primary-owned. G2 producer note
`notes/theory/2026-10-16-module-expression-carrier-correspondence.md` was read
at hash `57ba5d19388ad30fce91fb3368bd6e07032336c4c3dd62175b52df6e7211f085`;
the primary's explicit independent CLEAN receipt supplies its accepted review
status, rather than this producer certifying that note. The test file changed
from the first inspected `dc1351fd…` to the final hash above; runtime and HIR
dependencies did not change.

Commit packet: sole lease remains this file; original baseline 1a64937f1,
actual implementation hash set/read HEAD above; original derivation clean at
67f0c87f…, actual §10 review pending. Suggested checkpoint:
`research: bridge authentic mixed runtime roots to source scheduling`.
Shared-record delta for primary: consume this actual G4 bridge after its fresh
review, with the independently accepted G2 source theorem applied; retain broader OPEN parents and
separate cache-bearing Resume decision. Next action: independent delta review
against this frozen runtime/HIR set, followed by primary's coherent integration.

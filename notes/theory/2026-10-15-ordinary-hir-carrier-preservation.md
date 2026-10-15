# Ordinary HIR carrier preservation at the owning constructors

Status: independently reviewed constructive source derivation of the original
local preservation claim for the final implementation hashes below. The five
local formation conclusions are discharged; solver and F5 parents remain OPEN.

Independent proof review: `ordinary_carrier_semantic` accepted all five original
claims and actual-source bridges without findings at artifact SHA-256
`29a6ab734a2dc37d48613fc312941d37c7ccac05da46c34e3a75b07de1cf63af`.
Separate implementation/contract delta reviews are clean. Integration on
2026-10-16 preserves five copied source files exactly; `source_identity.rs`
only drops an extra EOF blank line (integrated SHA-256
`67c67e43243301cb15e7ecf4797e29fcc58c6dac496a83decfdfc448bd5037d9`). `lib.rs` additionally
contains the separately reviewed test-only grouped-spine repair `b5031d2fc` and
line wrapping of the new export list. Its integrated SHA-256 is
`f8bc70c4daad607e3acacc5d5a8dee8d9661ab959579879e4a6bc125578d09e5`.
Those differences change no production constructor in this derivation.

## Frozen statement and authority

The governing source is
[`2026-10-10-ordinary-hir-successor-carrier.md`](../design/2026-10-10-ordinary-hir-successor-carrier.md),
especially §§2–4 and its 2026-10-15 direct continuation. The primary selected
that unchanged binding-only scope using the current continuation and preserved
substantive approval. This note adopts no additional semantics.

Reference source baseline: `2dc90eaeb78dd9b13277bb3f41b6d10dbf60759a`.
The first pass used the reference constructors before implementation integration.
The primary then froze `/tmp/yulang-ordinary-source-carrier` and supplied the
six dependency hashes in the actual-source bridge below. No source from the
moving main workspace is used as the candidate implementation premise.

Reference dependency SHA-256 values:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/module.rs` | `70678eb23bf50813f77b7be3f90442c3b3faea2c754593cf6f35d3f7c0fcf645` |
| `crates/yu-hir/src/module/local_source.rs` | `0255329f6c3261d46f1108ca2fa7b9696441669ab2c70a43a17adac50708abaf` |
| `crates/yu-hir/src/module/source_annotation.rs` | `f8f8a1934d9961d443b2a0b55a79aa3272ec7cd820f7a40d9bd6217f3456ae38` |
| `crates/yu-hir/src/shadow.rs` | `676f003fb641a060e497c47ceb406a2fd1814a34d621758c34fc958c3b807612` |
| governing design at direct continuation | `2957f826b779f1bcf17f403c3968afb98861ec210d6d5eac948ff43906c287d3` |

Quantify over every `ModuleIdentity i`, `ParsedFile p`, and `SemanticImports s`
accepted as arguments by the existing ordinary `module::lower_module`. No new
parsed-source grammar restriction is a hypothesis. Let `O(i,p,s)` denote the
reference ordinary run and `N(i,p,s)` the carrier-bearing run. A genuine
availability failure is distinguished from an unsupported source body. For a
returned module define its **ordinary projection** to contain:

- identity, revision, source-order item sequence and all item payloads;
- the complete ordered errors, attachments, causal error references and
  diagnostics;
- each admitted `DefId` including same-name ordinal, each root's structural
  identity, every root parameter's owner/ordinal/name/range, and all ordinary
  expression occurrence ordinals;
- every ordinary name resolution, including parameter owner/ordinal and
  module-definition payload, and the existing definition-allocation metrics.

Cross-run comparison erases only the fresh artifact brand. It does **not**
erase occurrence ordinals or parameter owner information. Existing structural
`PartialEq` alone is weaker than this projection: `HirParameter::eq` omits its
ID and `ResolvedExpr::eq` omits occurrence IDs. Within a single returned module
the carrier must reuse the exact branded root and admitted parameter IDs.

Required conclusion for the original domain:

1. The ordinary phase of `N` follows the same admission, complete namespace,
   recovery, body lowering, diagnostics and identity-allocation constructors
   as `O`. If both return a module, their ordinary projections are equal.
   An additional genuine carrier availability failure may prevent a new
   module from being returned; an unsupported source form may not do so.
2. When `N` returns a module, exactly one outcome exists for every already
   admitted binding, in direct-root order: `Supported(authentic LocalSource)`
   or `Unsupported(root, source origin/reason)`. Rejected headers and direct
   expression roots have no such outcome. Unsupported does not add a HIR error
   or diagnostic and does not stop later roots.
3. A supported carrier is built from the same parsed snapshot, complete
   ordinary namespace, artifact, exact root and exact admitted parameter IDs.
   Additional source occurrence IDs are minted only after the final ordinary
   cursor, with roots and source children processed in source order.
4. A refused or failed carrier attempt publishes no partial occurrences,
   local IDs, parameter origins/owners, expression/binding/annotation/group
   arenas, or advanced occurrence cursor. A genuine identity, allocation or
   internal failure is an availability error, never `Unsupported`.
5. Different simultaneously observable lowering artifacts have different
   brands; foreign artifact queries fail before consulting a root map.

Here “publication” means exposure in a returned `HirModule`, or commit into
the sidecar state that a later root can use. Ordinary definition/parameter
origins that already exist before a carrier attempt are retained; they are
not partial writes of that attempt. No requirement to restore allocator
capacity is introduced. For process abort at an infallible Rust allocation,
there is no returned module; this is not a claim that arbitrary allocator
failure is converted into a `Result::Err`.

Excluded: default solver selection, acceptance of direct-expression carriers,
header expansion, F5 replacement, Call semantics, inferred types, effect hygiene,
generalization, soundness and principality. Retaining authentic source facts
does not prove those later conclusions.

## Reference invariant and actual source owners

For ordinary lowering, `LoweringCounters::default()` has both behavioral flags
false. Before iteration `j` of the root loop maintain:

`I(j)`: plans and namespace are the complete ordinary ones; `items` is exactly
the first `j` ordinary root products; `ErrorSink` is the ordered reference
emission prefix; the occurrence cursor is the next unused ordinary ordinal;
the artifact is the one root-loop artifact; `ScopeStack` is at the restored
root depth. Source-origin recording is a write-only sidecar action and cannot
affect any of those facts.

The owners and their independently inspectable required facts are:

| Owner | Reference fact / candidate bridge obligation |
| --- | --- |
| `module::lower_module`, `lower_module_with_counters` | Preserve ordinary false flags; complete ordinary loop before carrier work. No call to opt-in local-source lowering may replace this entrypoint. |
| `validated_recoveries`, `partition_recoveries`, `emit_structural_errors` | Use the same validated recovery sequence and attachment computation once, in the same order; no sidecar pass changes the sink. |
| `plan_root`, `plain_binding_header`, `identifier_pattern_name` | Preserve exactly the ordinary header predicate. Enabling `local_source` here admits annotated/call-style/multiple formals and is not a preservation proof. |
| `namespace` | Iterate only admitted plans in source order, assign the same per-spelling ordinal, retain the same complete name-to-`DefId` vector. |
| root loop, `DefinitionRootId::new`, `next_occurrence` | Create the same root and ordinary occurrence sequence before source work. Never mint a second artifact or replacement ordinary root. |
| `lower_plan`, `HirParameterId::new`, `ScopeStack` | Reuse admitted parameter IDs. Preserve lambda/body occurrence ordering and root-scope restoration. |
| `lower_direct_root_expression`, `lower_body`, `lower_simple_chain`, `lower_leaf` | Keep all ordinary missing/recovered/unsupported/resolved branches and their ordered `ErrorSink` effects. Source formation cannot supply a different ordinary projection. |
| `local_source::form`, `Builder` | Formation uses original root/parameters/namespace/snapshot; all mutable sidecar writes and the cursor are attempt-local until success. |
| `source_annotation::{form,parse_annotation,parse_expression_ascription,declarations}` | Annotation/declaration refusal is classified at its actual source owner; source-only declarations cannot emit ordinary diagnostics or alter ordinary admission. |
| ordinary sidecar finalizer and outcome lookup | One outcome per admitted binding; only a successful attempt commits; refusal continues; foreign-brand guard precedes lookup. |

The reference induction is direct. Identity mismatch is checked before planning.
`plan_root` preserves root-child order; only `BindingStatement` with the
ordinary plain header becomes `Binding`. `namespace` then assigns all duplicate
ordinals before body traversal, so body names see the same complete namespace.
`emit_structural_errors` first emits every validated recovery in its original
sequence and then distributes the already emitted IDs to root/value buckets.
Its `recovery_attachment` tests the original plan and recovery path, with no
body reinterpretation.

At root `j`, the loop consumes exactly one ordinary root occurrence. An
unsupported plan appends its existing error item; a direct expression follows
its existing simple-chain route; a binding creates IDs in admitted parameter
order, uses the first root occurrence for the first lambda, allocates further
lambda occurrences and then its body occurrence, and restores the lexical root
depth before propagating a body availability error. Duplicate-definition and
body semantic errors are appended at their original sites. With both flags
false, neither opt-in application traversal nor LocalSource projection is an
ordinary predecessor. `lower_leaf` resolves the same lexical parameter first,
then the same complete namespace. These three exhaustive `RootPlanKind` cases
establish `I(j+1)`. At loop completion all ordinary data and the final cursor
are therefore fixed before a sidecar continuation starts.

This establishes the **reference allocation/emission invariant** from its actual
owners. It does not yet establish that a moving candidate preserves it.

## Authentic successful formation from the existing builder

The needed authenticity claim has actual constructor support at the reference
baseline; it is not supplied by a later successful lookup. For every successful
`local_source::form` with the original inputs, maintain a slot invariant: each
reserved slot is either written once or owned by one pending formation
responsibility. `slot` appends one `None`; root/formal and local/formal loops
write the current Lambda and transfer responsibility to one fresh body slot.
The completion loop rejects any remaining `None`.

`OperatorChain` transfers current responsibility backwards through its finite
tail list: Ascription writes current and reserves one inner; Apply writes
current and reserves one callee and one argument, giving each exactly one
head/argument work item or immediate empty-call Unit. The operation path writes
the final current slot; otherwise the sole head work owns it. Group reserves
one inner. Block writes its incoming slot, gives one fresh slot to each local
initializer and one to its final expression. If reserves exactly its displayed
condition/body/else slots. Catch reserves one scrutinee and each displayed arm
body. Inline Lambda reserves one body and brackets its single body work with
Restore. Leaves write current. Restore and Publish do not write expression
slots. These are all expression dispatch arms; malformed alternatives return
an error rather than a partially initialized successful arena.

Every scheduled expression is a strict CST descendant of its scheduling source
node; siblings are disjoint proper subtrees. Synthetic root/local Lambdas use
finite parameter loops rather than rescheduling their statement. Proper finite
Rowan trees therefore give a finite expansion schedule, subject to explicit
identity/allocation refusal. No successful slot duplicates its owner. Every
`set` obtains its source key from the actual immutable inventory, its range
from that actual node, and an occurrence from the one passed artifact/cursor.
Annotation positions likewise come from that inventory. Catch binder IDs
retain the original arm key and binder ordinal; inline parameter origins retain
the actual Lambda key and direct binder-token range. No range-only origin
inference is needed.

Lexical preservation follows from `lexical`, `latest`, and each entry's
`previous` link. `push_binding` makes the newest spelling visible and saves
the previous entry; `restore(k)` restores exactly the saved prefix. Root
formals enter in their admitted order. Block initializers execute in source
order because their work is pushed in reverse: their self-local is present
only for a parameterized local, formal parameters may shadow it, and Publish
first restores the initializer prefix then installs that completed local.
The final expression sees preceding locals; the enclosing Restore removes
them. Inline Lambda installs its authentic parameter above a saved prefix,
and its entire body executes above the corresponding Restore. Catch body
binders enter only in the individual arm bracket; the scrutinee executes
before those arm brackets. Conditional children each begin at the saved
enclosing prefix. Thus Name copies the actual nearest lexical identity or,
when absent, the original complete ordinary namespace outcome. Failure while
forming any child is not successful restoration or successful formation.

`next_parameter` begins at the number of exact passed ordinary formals;
checked increments allocate disjoint local/inline parameter IDs. Local IDs
use the binding-vector ordinal. Named-group IDs use the next group-vector
ordinal and are retained before their initializer body work proceeds, with
the exact formal-to-Lambda list, final Lambda/body slots and original owner.
Inline Lambdas inherit the enclosing group rather than inventing a named
header. Consequently the successful source's ownership, scopes and resolution
IDs are constructor-derived. This is the local source formation theorem,
subject to the unchanged supported grammar; an unsupported body is represented
by the separate total outcome contract, without narrowing ordinary HIR inputs.

The reviewed [flat builder derivation](2026-10-13-flat-local-source-formation-proof.md)
and [inline constructor bridge](2026-10-15-inline-lambda-hir-formation.md)
explain related earlier transformations. The argument here rechecks the current
dispatch including If, Catch and named-group paths, rather than importing their
historical dependency hashes as current implementation evidence. The candidate
must preserve this argument or supply the exact changed constructor step.

## Complete attempt mutation cone

The reference builder does not itself give atomic refusal: its `set` records an
occurrence immediately and advances the caller's cursor. Its block branch can
record local identities and parameters before a later child refuses. Therefore
“the builder returned no LocalSource” does not entail “the sidecar is unchanged.”

Every field in this cone must have an attempt-local owner, or an independently
proved equivalent atomic construction:

| Construction | Mutable facts |
| --- | --- |
| `Builder::set` | occurrence-to-source map, occurrence cursor, expression slot |
| `Builder::block` | local map, parameter-origin map, `local_parameter_owners`, local binding/parameter/expression arenas |
| inline `LambdaExpression` | inline parameter origin, parameter ordinal cursor, lexical entry/restore work, lambda/body slots |
| `Builder::catch` and `Work::CatchArm` | catch binder IDs, arm sources, pattern/binder vectors, lexical entries and arm-body work |
| root and local named formals | named-group IDs/owner/enclosing/group/formals/terminal slots, root parameter references, local parameter cursor |
| annotation/ascription construction | full annotation types/effect rows and authentic keys, including any refusal after prior builder writes |
| declaration preparation | effect declarations and both effect/operation namespace maps; ordinary ErrorSink must not be a target |
| root outcome publication | outcome vector/map and any supported-source index; reserve/check before committing staged identities |

`HirSourceIdentity` at the reference baseline contains `parse_root`,
`definitions`, `occurrences`, `parameters`, `locals`, `local_binding`, and
`local_parameter_owners`. `parameters` includes both identifier-pattern and
inline-lambda origins. Staging only occurrences and locals misses real writers.
Catch binders and named groups are retained inside the source arena, so that
arena must also stay private. An annotation parse uses immutable counters at
its reference entrypoint; its returned annotation still belongs to the
attempt's unpublished source value. This enumerates actual writers rather
than assuming a transaction annotation covers them.

For a staged implementation, the atomicity induction is over admitted roots.
Let `S_k` contain committed outcomes/identity maps and cursor `c_k`. A root
attempt starts with private state `T_k` and a private cursor initialized at
`c_k`, sharing only immutable source/namespace/owner inputs. Successful
formation plus all publication preconditions commits exactly its complete
payload and final cursor; source refusal drops `T_k`, appends only its explicit
unsupported outcome, and keeps `c_k`; genuine failure returns an availability
error without a module. This induction is applicable only after source inspection
shows that **all** rows above target `T_k` and that publication itself has no
fallible operation after the first shared mutation.

## Identity, grammar, and order seams requiring actual code

The authentic-key argument begins at `source_keys(parsed)`, which indexes
`parsed.source_root()` descendants by their actual `SourceNodeKey`. It is not
a range-only join. `LocalSourceIndex`, local IDs, group IDs, catch binder IDs,
and parameter IDs retain the original root owner. `form` clones each passed
ordinary parameter's ID when forming root lambdas. Each builder `set` uses
the passed artifact; it cannot generate an ordinary occurrence retroactively.
The candidate must retain these source owners when moving them out of shadow.

The reference `invalid()` uses `StructuralProjection` both for unsupported
grammar/recovery and for missing source keys/sidecar, missing initialized slots,
and required named-group data. `source_annotation::unavailable()` likewise
covers source rejection and absent keys. A catch-all conversion of that error
to Unsupported would misclassify real internal failures. The candidate needs
an actual owner distinction, or a source-derived proof that each internal
failure branch is unreachable under its maintained call invariants. It cannot
silently assume every `StructuralProjection` is source unsupported. A new error
enum is not itself a theorem requirement; preserving the required distinction
at the actual owners is.

The reference builder emits outer application tails in reverse order before
processing the head and queued arguments. Its emitted occurrence order is
therefore not CST child order merely because root iteration is source ordered.
The required source-child allocation order needs an explicit candidate
construction: for example, a total order over all retained expressions derived
from the source-node traversal, with a stable tie order for several expressions
at one source key, followed by minting at the final ordinary cursor. Such an
owner may reassign only unpublished source occurrence IDs. It may not renumber
ordinary occurrences or reconstruct source identity from ranges.

Artifact equality uses `Arc::ptr_eq`, not the wrapping diagnostic serial.
Two retained nonzero-sized artifact allocations are distinct; source/root/
parameter equality keeps that brand. The lookup owner must reject a foreign
root even when its `DefId` payload equals a local root. This is a within-run
authenticity check, separate from the cross-run ordinary projection theorem.

The downstream boundary is concrete: at the reference baseline
`yu-solver::ConstraintBatch::collect` passes `candidate_values = false` into
the existing collector, and `SolvedModule` retains its original `Arc<HirModule>`
and frozen projections/schemes. A HIR-owned supported-carrier accessor can make
source evidence available without changing either choice. This note does not
infer a collector migration merely from source-map storage.

## Actual frozen implementation bridge

The primary supplied the following frozen dependency set for the second pass;
`sha256sum` against the isolated files matched all six entries:

| Candidate path under `crates/yu-hir/src/` | SHA-256 |
| --- | --- |
| `module.rs` | `1186152a7333056c875f51114293cc51dff0820a39e8591a934874fbf69de753` |
| `module/local_source.rs` | `9b78692c98b441412a4ac3db65b85276c4f0cdf9f222964a86553896d12a983a` |
| `module/source_annotation.rs` | `d67739edab321d5296775148351fa5e0b16d125b828b9cbf3a1eee394e1f3972` |
| `lib.rs` | `9fc4559d9692f3e304b73a734360251d9fa846ad68a107d867c053cc722fdcb0` |
| `shadow.rs` | `779ac9244296f9c710ae31308404e447ede53f9a567f6b1ded71c4ab7aa65c83` |
| `source_identity.rs` (new owner) | `af26ca6ebb84fa34fdc847b7027817dc9b08bda68d5b325f558407359dfe9b83` |

The primary clarified the original namespace premise: authenticity means
structural source formation under the **actual completed ordinary environment**.
Ordinary Act declarations remain rejected and do not create an effect/operation
namespace in this gate. A supported carrier can coexist with the existing
ordinary Error body, and can retain Unresolved operation evidence. Neither
Supported nor retained source erases a HIR error or authorizes a collector to
admit that declaration. No equality with the broader opt-in namespace or
semantic acceptance is asserted. This uses the original ordinary-environment
quantifier and is not a new source restriction.

### Ordinary projection and outcome coverage

At `module.rs:891–902`, the ordinary entrypoint creates the source inventory
and sets only `ordinary_source_carriers`; both `local_source` and
`shadow_applications` remain their default false values. The source inventory
is built directly from `parsed.source_root()` by `try_source_keys`; its fallible
map/work reservations return IdentityExhausted. It does not parse, associate,
emit errors, or choose a namespace. The internal ordinary identity check and
all original prepasses then run as before (`module.rs:942–1002`).

The ordinary loop at `module.rs:1009–1058` has precisely the reference
`RootPlanKind` split, root and occurrence construction, parameter/body/lambda
allocation and ErrorSink call sites. Enabling ordinary provenance merely
records the already selected definition/parameter/leaf origin; those map
writes return no alternative admission, resolution, occurrence or sink result.
`plain_binding_header` still reads the two false behavioral flags; every
ordinary header branch therefore agrees with the reference. `lower_plan`
cannot enter pre-body `local_source::form` or its formed projection; the
ordinary body follows its reference association route. Consequently `I(j)`
applies by the exhaustive three-case induction already given. At loop exit,
the complete ordinary item/error/diagnostic/identity projection and cursor c
equal the reference projection modulo its fresh artifact brand.

At `module.rs:1061–1076`, only now does the implementation zip the unchanged
plans and completed items. There is one item per plan; a Binding item is
created exactly in the admitted Binding branch. Filtering by that completed
item thus selects precisely all admitted bindings, in direct-root source
order, with their exact root and boxed parameter slice. `form_ordinary`
receives those references and the original complete ordinary namespace.
The output vector appends one outcome and its index under the same root.
Different admitted roots are distinct because `namespace` assigned each
same-spelled header a different checked ordinal. No root can overwrite an
earlier outcome index. Both output container reservations precede that output
insertion. If either fails, `?` aborts the module before publication.

### Actual isolation and refusal/availability branches

`form_ordinary` at `local_source.rs:462–503` takes the private committed identity
value into `identity`, installs `identity.empty_stage()` in counters, and gives
`form` a private `staged_next`. `empty_stage` retains only the parse-root key;
all definition/occurrence/parameter/local/owner maps are empty and the optional
shadow-only `local_binding` is None. It shares no mutable map with the committed
identity. The temporary `local_source = true` permits the existing *local*
header grammar only after ordinary lowering has finished, and is restored
immediately when `form` returns.

Reinspection of every writer in the mutation-cone table establishes that
Builder writes only the installed identity maps and its fresh local vectors,
maps and worklist. The parameter cursor belongs to that Builder. Catch
patterns/binders and named groups are in those fresh vectors; annotation
formation reads immutable counters and returns private annotation values.
There is no builder write into ordinary items, sink, namespace, artifact,
source-node inventory or committed identity. There is no ordinary-call
declaration-preparation step: effect/operation namespaces remain the original
empty ordinary environment. The optional `local_binding` field has no writer
in this call cone. This establishes the full isolation premise directly.

On `FormationError::Unsupported(reason)`, the private stage and staged cursor
are dropped, the original identity is put back, and the result contains just
the original root/key/reason. The owning outcome loop appends that result and
continues to the next binding. On `Availability(error)`, the identity is
restored and `Err(error)` propagates immediately through the outcome loop;
there is no returned module or subsequent-root retry.

On success, the source is complete by the slot/provenance/lexical argument
above. `order_occurrences` still operates only on that private source and
stage. Its `?` paths can leave `counters.source_identity = None` and drop the
private original identity. This does not satisfy a general retry/restoration
contract for arbitrary calls to `form_ordinary`, and no such claim is made:
the **actual** caller immediately propagates Err and never exposes counters,
a later root, or a HirModule. The externally owned occurrence cursor is still
unchanged. Full private-state restoration is unnecessary for this publication
theorem under the top-level abnormal-path principles.

### Occurrence order, exact identities and publication

`order_occurrences` at `local_source.rs:97–125` first groups every completed
expression index under its authentic source key, retaining ascending arena
order within a key. It clears only the stage's temporary occurrence map,
resets the private cursor to the original c, and visits
`plan.node.descendants()`. The pinned Rowan 0.15.17 owner implements
`descendants` as Enter events of preorder, and `Preorder` starts with Enter
of its own root then descends first-child/next-sibling (`cursor.rs:721–739`,
`1177–1230`). Thus root formals, whose source is the root plan itself, are
included. Each encountered group is removed once and assigned the consecutive
checked IDs c, c+1, …; if a group is not reached, leftover groups produce an
availability error rather than a partial supported result.

Every successful expression source belongs to the original plan subtree by
the builder descent argument. Supported expression origins have positive
source extent (named statements, identifier/literal nodes, application tails,
delimiters, lambda/If/Catch/block nodes); distinct such source occurrences
cannot share the same green allocation and starting offset in a finite proper
tree. Intentionally repeated source keys belong to multiple synthetic records
at the same original node and use their stable arena order. The grouping
therefore gives exactly original CST preorder with that explicit same-key tie
order, independent of the earlier application-tail work order.

Only `LocalSourceExpr.occurrence` and the stage occurrence map hold the
temporary minted IDs: bindings, groups, scopes and forms link expressions by
`LocalSourceIndex`, and annotations/parameters link by their original owners.
Replacing every expression occurrence and rebuilding that map leaves no
temporary occurrence reference. Every published source ordinal is at least c,
strictly above the maximum ordinary ordinal, and uses the original artifact.
No ordinary expression or parameter ID is renumbered. Each root Lambda copies
the exact parameter ID passed from the completed binding.

`append_stage` at `source_identity.rs:73–94` checks parse-root equality,
absence of overlapping occurrence/parameter/local/owner keys, and an empty
staged definition map. Its four fallible reservations all occur before any
map extension. The subsequent extensions have reserved capacity and move the
complete stage maps. No Result-returning operation follows the first map
extension. Root parameters were recorded in the ordinary identity, while the
stage records only local/inline parameters from checked ordinals R onward;
different roots have different owners. Fresh ordered occurrence suffixes and
per-root local identities similarly establish the expected disjointness from
the actual constructors; the checks also reject an internal violation.

After append succeeds, `form_ordinary` restores the combined identity, then
updates the external cursor and returns the complete Supported source. Any
failure to reserve the later outcome containers aborts the whole still-private
module. A final `Ok(HirModule)` is constructed only after every root outcome
has been appended (`module.rs:1078–1093`). The root induction therefore gives
the required no-partial-publication and later-root continuation properties.
Reservations may change private capacities on failure; arbitrary infallible
allocation abort recovery is outside the frozen statement.

### Failure classification and consumer authentication

The classification premise is now emitted at the actual owners.
`FormationError::{Unsupported,Availability}` is distinct at
`local_source.rs:24–39`. The ordinary adapter pattern-matches those variants;
the conversion of Unsupported to legacy StructuralProjection is used only by
the existing opt-in availability API and does not collapse the ordinary result.
`invalid()` is Availability(StructuralProjection): absent keys, absent
identity, unfinished slots and missing required group facts use that route.
Every checked identity increment/conversion and fallible reservation propagates
HirAvailabilityError into Availability. Recovery and retained depth limits
have their own Unsupported reason; the remaining unsupported branches test
actual CST syntax/topology or supported-form grammar. There is no catcher
that turns those genuine availability failures into an unsupported outcome.

`source_annotation` separately maps missing source keys to availability at the
declaration, annotation and row constructors. Grammar/recovery/ambiguous or
absent source effect names are source refusal; its depth preflight returns
SupportedDepth. Header/node downcasts used by source-refusal branches are
actual CST-shape checks; the original ordinary plan/validated local header
invariants supply the required header/pattern at the normal callers. They do
not catch an identity or allocation error. Annotation parse does not mutate
committed state, even when it refuses after earlier stage writes.

Finally `HirModule::source_carrier` checks `owns_definition_root` before index
lookup (`module.rs:810–815`); `local_source` goes through that guard before its
Supported/Unsupported/opt-in-map selection. Ordinary outcomes are total, so
the opt-in map fallback is not taken for an admitted ordinary root. Foreign
artifacts fail InconsistentIdentity even for equal structural DefIds. The
same Arc-branded identity argument used by the reference source remains valid.

Thus all five frozen local conclusions are derived for that actual source set,
including every ordinary input and every actual Result-returning failure path.
This is an unreviewed constructive derivation, not independent certification,
and does not close any solver/Call/effect/inference/F5 conclusion. The known
literal-spelling repair and default provenance API/export changes were absent
from this first snapshot. The final delta bridge below supplies the actual
changed-owner argument; these first-snapshot hashes remain historical inputs.

The added ownership costs are explicit. `try_source_keys` walks the module
once; after ordinary lowering each admitted root has one recovery preflight,
the existing flat builder, one source-key grouping pass over retained
expressions and one CST preorder remapping pass. Admitted root subtrees are
disjoint, so those new root preflights/remapping walks do not multiply module
node count by the number of bindings. Staging starts with empty maps and does
not clone earlier roots' accumulated identity maps. `append_stage` visits each
new key for overlap checks then moves that stage's entries once; it does not
rescan the entire committed identity. The extra grouping map retains O(E)
indices/key references for E formed expressions, in addition to the complete
temporary source and staged maps. Original builder header/annotation scans,
spelling/key hashing/copying and allocation costs remain explicit rather than
unit-cost assumptions. Under ordinary amortized vectors and expected HashMap
behavior the added inventory/order/merge work is linear in visited nodes and
formed records plus those real payload costs. No timing/RSS or arbitrary
allocator-failure bound is inferred from this structural accounting.

## Final repair delta and current frozen dependency set

The primary supplied a final frozen repair in the same isolated directory.
All six supplied SHA-256 values match the actual files. These are the current
implementation dependencies for the theorem; they supersede the six
first-snapshot candidate hashes, without changing the original statement,
quantifiers, ordinary namespace, supported ordinary inputs or exclusions.

| Final candidate path under `crates/yu-hir/src/` | SHA-256 |
| --- | --- |
| `module.rs` | `c32e3e61df7a4ce4cf4e2b29c1728f14083bd3821dcba2eb56b1f60a81b9fce5` |
| `module/local_source.rs` | `13c134afb7f85996c2f12fd27fbb78ab640878611287ca4952c10fd48cfd4c81` |
| `module/source_annotation.rs` | `eea39d10383bd76e6307f059f6f502633aaadcb9adea3aba33f9f385f0a39acc` |
| `lib.rs` | `f22ee43a4743bcda5d8a96d234af3d2121a8c5bd809c33dddf906080b83d86c0` |
| `shadow.rs` | `87f19092a202e87083cdf8f41b66f8f8ed8f9358020a5e5b5a0c48cc2323c067` |
| `source_identity.rs` | `eb0f1a65dccdbdfef9db9aec4d88f3a6e6cb0b8cf9a5bf41fb00701cb4c2549d` |

**Ordinary phase and transaction owners.** Reinspection finds the same default
false behavioral flags and original phase boundary at `module.rs:913–923`,
`1030–1097`. `form_ordinary` at `local_source.rs:488–529` preserves the actual
empty-stage, private cursor, error split, remap, checked merge and cursor
publication established above. `order_occurrences` is unchanged at lines
97–125. `source_identity::empty_stage` and `append_stage` retain the same field
coverage, disjointness checks, all-before-publication reservations and complete
map moves. Renaming the retained parameter-origin type does not change its map
keys or payloads. Therefore the ordinary projection induction, outcome
coverage, exact identities, source ordering and publication proofs carry over
at their actual owners, independently of tests.

**Feature boundaries.** Source declarations and helpers used only by existing
shadow adapters are now precisely guarded by `cfg(any(feature = "shadow",
test))`. The ordinary source identity, keys, typed parameter origins,
LocalSource forms/annotations and ordinary outcome entrypoints remain present
without that feature. The formed simple-body projection's Atom arm and
`direct_atom` computation are guarded too; the default `form` returns an
Unsupported projection value while returning the same completed source.
`form_ordinary` discards that second tuple component. Consequently this cfg
change cannot change ordinary HIR, formation, failures or source publication.
With shadow enabled, the old adapter projection still has its original owner.
No rejected Act is promoted into the ordinary effect namespace.

**Provenance consumers.** The final `HirModule` exposes
`definition_source_key`, `occurrence_source_key` and `parameter_source_origin`
at `module.rs:827–846`. Each first checks the exact artifact brand, then returns
a borrowed existing map payload; an absent mapping returns None, without
reconstructing a source key or a binder. Definition/occurrence queries use
their own original ID; the parameter query checks its root brand and uses the
full parameter ID as the map key. This admits retained local/inline origins
without fabricating a root formal or local owner. The exported
`HirParameterSourceOrigin` retains either the exact IdentifierPattern key or
the exact inline Lambda key and direct binder range. The original root-formal
ownership predicate is unchanged. The shadow typed-position consumer aliases
that same origin type and keeps its parse ownership, exact Lambda/direct-token
and ambiguity checks. These read-only consumers cannot affect ordinary output
or turn an uncommitted stage into available provenance.

The approved earlier test assertion that an ordinary artifact lacks a source
identity is superseded by this intended carrier retention. That absence was
never an ordinary-projection theorem hypothesis: the frozen projection
preserves original items/errors/diagnostics/identities, not absence of the newly
authorized sidecar. Added tests are outside the derivation's premises and were
not executed by this leaf.

**Literal owners.** At `local_source.rs:414–439`, `integer_spelling` filters only
the existing trivia kinds, requires exactly one direct Integer token and
returns that token's exact text. `string_spelling` requires the direct
StringStart and StringEnd delimiters in order, with no extra delimiter, then
slices the actual node text from the first delimiter's start to the last
delimiter's end. Subtracting the actual node start translates authentic Rowan
coordinates; the checked UTF-8 slice preserves every byte between those
delimiters, including interior whitespace and heredoc content, while excluding
exterior trivia. No independent range/spelling inference is used.

The actual literal dispatch at lines 1005–1017 calls these helpers and retains
the original source node, key, range, index, scope and group. String
interpolation still follows the existing explicit source-refusal branch.
Integer/delimiter inconsistencies are Availability(StructuralProjection),
not a mislabeled Unsupported or a partial successful literal. On normal
parser-produced recovery-free literals these checks do not introduce a source
restriction: `emit_integer_core` encloses the one actual Integer item;
`string_literal_with_interpolation_body` starts with StringStart and returns Complete only
after emitting StringEnd and closing that node. A boundary path emits Missing,
which is already caught by the root recovery preflight. Non-interpolated
content cannot introduce another direct string delimiter pair. Thus the
literal repair restores authentic payload extraction for the original parser
domain and leaves the original ordinary projection and carrier failure safety
proof unchanged. No string decoding/runtime theorem is asserted.

The additional inspected literal source owners have SHA-256:

- `crates/yu-syntax/src/cursor/recovery/emit.rs`:
  `de091c117486f7990dc6872bf2ee7659c0e3e7e148e255f47b56b7836fe7c59d`;
- `crates/yu-syntax/src/literal/mod.rs`:
  `d54b4ef01cb3c9d46048b5638f9837eb050816a5e7edd35460f20cf1e557fd40`.

All five original local conclusions therefore retain their constructive
actual-source derivation for the final frozen dependency set. No proof premise
has been narrowed to a fixture or to a newly restricted ordinary source
grammar. The derivation is ready for fresh independent review; its producer
does not certify review success or parent closure.

## Evidence and handoff

Method: static owner tracing and construction induction; no checker, finite
probe, test, build, compiler-code edit, or semantic change. This is a source
bridge assignment, not a new Simple-sub inference proof. No repeated failed
proof variants or new reconstruction layer were introduced.

Requested runtime: normal `prover`, GPT-6.1 Sol/high. The callable schema
contains `prover`; `.codex/config.toml` registers it and defaults subagents to
GPT-6.1 Sol/high; `.codex/agents/prover.toml` omits model/effort pins. Observed
effective runtime model/effort metadata: unavailable/unknown. No Astra request,
child dispatch, or additional process lane occurred.

Second-pass checks: six supplied candidate hashes matched; static owning-source
inspection covered the complete ordinary entrypoint, form/adapter, every builder
writer, annotation failure sites, identity-stage merge, occurrence ordering and
lookup. The additional inspected syntax owner `crates/yu-syntax/src/full_parse.rs`
has SHA-256 `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8`;
isolated `Cargo.lock` has SHA-256
`2055b82e7c2c68df727940d7053da0490368a99217bd3587866a7003177484e6`
and pins Rowan 0.15.17. No executable result was used as a proof premise.
No Cargo, test, probe or Git command ran in the second pass; resource use was
bounded static shell reads, zero heavy processes/measurement samples and no
RSS measurement. No code or dependency was changed by this leaf.

Final-pass checks matched all six supplied final hashes and inspected the
changed provenance, literal, cfg and unchanged transaction/ordinary owners.
No code, Git operation, Cargo invocation, test, executable probe or measurement
was performed in this pass. This proof note is now frozen for independent
review. Requested/observed runtime and resource boundaries remain as reported
above.

Next action: primary obtains fresh independent review of the final frozen
source derivation. The ordinary implementation parent stays OPEN until
required verification/review and integration are accepted.

# Module expression carriers at the actual HIR constructors

Date: 2026-10-16
Status: constructive source-to-implementation derivation; fresh independent
proof review CLEAN for the five original G2 preservation claims. G3/G4 and the
original native/runtime parents require their own evidence.
Reference baseline: `1a64937f1`, supplied by the primary.
Exclusive output lease: this note only. Actual frozen HIR input hashes appear
in §9. Concurrent solver/runtime changes are excluded.

Integration review: compiler-referee `ordinary_carrier_semantic` returned CLEAN
at producer SHA-256
`57ba5d19388ad30fce91fb3368bd6e07032336c4c3dd62175b52df6e7211f085`.
All six production HIR hashes in §9 remained unchanged. Subsequent focused-test
setup replaces bare `@` (not an admitted expression) with `f(@missing)` (an
admitted recovered expression), preserving the recovery assertions. Its verified
hash is `36ec22c58cf790ed910ed4af93d6f9a860263efe6a5fa3fdefb7291ad3c03fbf`;
the older §9 evidence-only test hash records the producer snapshot. Tests are
supporting evidence, not premises of the preservation proof.

## 1. Frozen statement, domain and exclusions

The Authoritative [module-expression source-owner design](../design/2026-10-16-module-expression-source-owner.md),
especially authentic source root §1, extends the binding carrier domain while
retaining the [direct-root slice](../design/2026-09-20-hir-direct-root-expression-slice.md)
and [ordinary carrier contract](../design/2026-10-10-ordinary-hir-successor-carrier.md).
The [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
govern necessary abnormal-path safety. The independently reviewed
[ordinary preservation proof](2026-10-15-ordinary-hir-carrier-preservation.md)
establishes the earlier constructor/transaction lemmas. Below those lemmas are
applied to their actual changed owners, rather than assumed of a new adapter.

Quantify over every ModuleIdentity, ParsedFile and SemanticImports passed to
ordinary `lower_module`. No new parser, expression-shape or namespace premise
is imposed. An actual direct root means exactly an original direct root
classified `RootPlanKind::DirectExpression`, which the unchanged lowerer returns
as `HirItem::Expression`, including an Error expression. Rejected nonexpression
items remain outside that classifier; the extension does not reclassify them.

Compare the baseline ordinary run O and modified run N on these same inputs.
For returned modules compare the full ordinary projection: source-order items
and payloads, identity/revision, ordered errors/attachments/causal references
and diagnostics, DefIds and duplicate-name ordinals, ordinary occurrence
ordinals, parameter ordinals/owners, resolutions and existing definition-root
allocation metrics. Cross-run comparison replaces only the fresh artifact
brand and embeds an old definition owner d as SourceRootId::Definition(d).
It does not erase occurrence ordinals. This injective owner embedding preserves
all old equality relationships, without claiming unchanged numerical Hash
outputs or representation bytes for the deliberately generalized API.

Required conclusions for a returned ordinary module:

1. Every and only actual direct expression has a private authentic root
   anchored to its original item occurrence; foreign and nonroot child
   occurrences cannot authenticate one.
2. The ordinary projection and every old binding-carrier identity are
   preserved under the preceding comparison. Within N, root handles and root
   formal IDs are exact reused branded values, not cross-run reconstructions.
3. Every actual binding and direct expression has exactly one source-ordered
   outcome, Supported or Unsupported. A supported expression body has its
   original direct-item occurrence. Other new expression occurrences are
   allocated after the complete old binding-carrier suffix.
4. Every generalized source-local owner, scope, origin and reference is exact
   for its actual source root. Resolution remains relative to the original
   completed environment of that entrypoint.
5. A refused/recovered attempt commits no partial carrier delta or cursor;
   later roots proceed. Genuine identity/internal/allocation failures remain
   availability errors and publish no partial module.

Also compare baseline and modified `lower_module_with_local_source` on every
input for which that existing opt-in entrypoint returns. Its binding sources
remain single-owned in its existing binding map; expression outcomes are added
after the entire old lowering pass. The ordinary and opt-in environments need
not agree: in particular rejected ordinary Act declarations do not populate an
ordinary effect namespace. Supported means authentic structural formation,
not semantic acceptance or absence of existing ordinary HIR errors.

Additional genuine availability failure may prevent N from returning where O
returned. Neither unsupported source syntax nor recovery is relabeled as
availability to satisfy this theorem. Infallible allocator aborts are outside
Result-returning failure safety. No solver receiver, native interpretation,
type soundness/principality, runtime execution or G3/G4 conclusion is asserted.

## 2. Exact source owners and ordinary prefix induction

At `module.rs:989–998`, ordinary `lower_module` still enables only
`ordinary_source_carriers` after retaining parse-owned identity/keys. Both
behavioral flags `local_source` and `shadow_applications` remain false through
planning, namespace construction and the entire ordinary root loop.

The diff against `1a64937f1` leaves the admission predicate, `namespace`,
recovery partition/error emission, `lower_plan`, direct-expression/body/leaf
lowering and ErrorSink behavior unchanged, apart from the explicit definition
owner embedding at parameter construction. In particular `plan_root:1430–1475`
selects only original OperatorChain direct expressions and original admitted
binding headers. `namespace:1477–1501` still visits only binding plans and
assigns duplicate ordinals before any root is lowered.

Use the original ordinary loop invariant at `module.rs:1099–1165`: before root
j, the item/error/diagnostic prefix, ordinary cursor and lexical scope equal
O's, modulo its artifact brand and owner embedding. The new expression-root
branch consumes a clone of the root occurrence already allocated by the same
`next_occurrence`; it neither calls that allocator nor writes the namespace,
scope or ErrorSink. It inserts only root/source provenance. Definition root
construction and ordinary parameters otherwise use the same admitted IDs and
checked ordinals. The unchanged lowerer therefore establishes the invariant
for j+1. A new reserve/source-key failure returns availability before a module
is exposed. Successful completion establishes the complete original ordinary
projection and cursor, including ordinary Error expressions and original
diagnostics. No source carrier has yet changed that ordinary projection.

The new postpass has no mutable item, sink, namespace or ordinary expression
reference. Its constructor arguments at `module.rs:1173–1193` are borrowed
plans/items, immutable completed namespace, the exact root/formal slice, and
private counters/cursor. Consequently subsequent formation cannot rewrite an
ordinary result or replace its error with a successful structural carrier.

## 3. Authentic expression roots: both directions

`ExpressionRootId` has one private field, an original HirOccurrenceId
(`module.rs:225–232`), and no public constructor or ordinal conversion.
At `:1106–1118` its sole production constructor occurs iff the current plan is
DirectExpression. It stores exactly the occurrence just allocated for that
ordinary item. `lower_plan:1514–1539` sends that plan to
`lower_direct_root_expression:1650–1723`, whose recovery, unsupported and
resolved branches all return Expression with that original outer occurrence.
No supported structural source assumption is needed for this root registry.

Conversely no binding or Unsupported plan enters that constructor branch.
Ordinary root allocation is checked and strictly increasing; later child IDs
cannot equal an earlier root ID. Therefore the returned root map is in
bijection with actual direct Expression items, at their original occurrences.

The public `expression_root(:846–851)` first checks artifact ownership, then
looks up that exact occurrence. Thus a foreign occurrence returns
InconsistentIdentity, and a same-artifact child or binding occurrence returns
None, even if it has the same source range or spelling. The private handle's
equality includes the occurrence's artifact identity. `owns_expression_root`
requires exact membership, not merely a matching artifact; `owns_source_root`
and `source_carrier_for(:852–865)` retain that check. A foreign cloned root is
not admitted. Public enum construction SourceRootId::Expression requires an
already obtained private root; it grants no constructor for another occurrence.

`source_identity.expressions` records the original plan node key at root
formation, independently of body simplification (`module.rs:1111–1116`).
`expression_source_key` and `source_root_source_key(:894–907)` authenticate
before consulting it. The root's direct-item key and a body record's more
specific source key are deliberately separate; their occurrence identity is
the preserved link. A supported leaf can have an IdentifierExpression or
IntegerLiteral origin within that original OperatorChain root.

## 4. Preserve old binding IDs before adding expression children

`module.rs:1167–1182` completes the entire ordinary binding-carrier pass first,
in the same binding order as O. A binding's passed owner is precisely
Definition(binding.definition_root.clone()); its parameters are the exact
already completed boxed parameter slice. In `local_source::form`, the
Definition branch still selects the old Definition scope, admitted header,
body extraction, named root group and root annotation. Every root formal
copies its existing `parameter.id` (`local_source.rs:598–630`). No fresh formal
is substituted.

For Definition owners, both `Builder::set(:824–830)` and
`order_occurrences(:120–126)` take their unchanged allocation branches. The
builder, lexical resolution, local/inline parameter cursor, local ordinal and
group ordinal operations differ only by the injective owner embedding. By
induction on the old worklist transitions, the same successful binding emits
the same payload/ordinals and reaches the same cursor; the same refusal emits
the same reason and leaves that cursor unchanged. Annotation parsing changed
only its owner parameter type. Therefore every old binding-carrier ordinal
and equality relationship survives, including in mixed modules whose first
item is an expression. An expression does not consume a DefId duplicate
ordinal, a DefinitionRootId allocation metric or an old parameter ordinal.

Only then does `module.rs:1183–1194` visit expression items in original order.
Each receives its already authentic root and an empty root-formal slice.
`form` uses the original entire plan node as its body chain, starts in
ModuleExpression(root), creates no named root group and adds no fabricated
root binding annotation (`local_source.rs:565–635,715–721`).

## 5. All source constructors and exact generalized owners

The induction invariant is over actual Builder work transitions, not source
fixtures. Every expression slot and newly constructed source-local identity
uses the same borrowed SourceRootId; every source key is looked up from the
same immutable parse inventory; all child references use checked per-root
LocalSourceIndices. The worklist has the unchanged lexical stack/latest map.

| Actual transition | Owner, source and reference preservation |
| --- | --- |
| `slot`, `parameter_id`, `next_named_group` (`:739–747,789–806`) | Clone exactly Builder.owner; retain checked arena/parameter/group ordinals. Slot indices and group lookup reject another owner. |
| Integer, Boolean, String, Name (`:1004–1078`) | Original source key/range and authentic literal payload; lexical resolution first, then the same complete module namespace; Unresolved/Ambiguous evidence remains explicit. |
| Operation and application chain (`:852–971`) | Original path/tail key and source form; Apply children are newly owned slots; implicit Unit retains its actual call tail. Operation resolution reads the existing effect/operation namespace, never creates an expression-owned declaration. |
| Ascription and Group (`:869–889,1062–1080`) | Same owner through original annotation or parenthesized source; inner reference remains an owned slot. No fabricated Lambda or binding. |
| Inline Lambda (`:972–1003`) | Fresh checked parameter ordinal under this source root; exact Lambda key plus binder token range; body scope references that same parameter, and Restore removes its lexical entry. |
| Local block/initializer (`:1231–1358,650–704`) | Local ID, parameters, local-parameter-owner map and annotations share Builder.owner; initializer scopes refer to that local; temporary named self binding and parameters restore before publication into the block's lexical environment. |
| Named local group (`:654–692,808–814`) | Group ID uses source root; owner is the actual Local ID, with original enclosing group and ordered formal/Lambda/terminal-body indices. Expressions have no root Definition group. |
| Catch (`:1100–1180`) | Binder ID includes this source root, exact arm key and binder ordinal; scrutinee/arm slots, CatchArm scope and parameter/continuation references are actual retained ones; each arm restores its lexical environment. |
| If (`:1181–1230`) | Original ordered conditions/bodies/optional else with owned indices; each child starts in the enclosing lexical environment. |

The transitions cover every successful LocalSourceForm variant and every
recursive Work variant. Other shapes return the unchanged typed refusal;
recovery is refused before work (`:561–563`). This covers all genuine direct
roots by an outcome, including forms outside the structural carrier grammar;
it does not silently promise Supported for every parsed expression.

The root/child induction is finite: recursive Expression work follows proper
CST children; initializer work follows original binding bodies; Restore and
Publish discharge finite installed scopes. A successfully consumed slot is
filled once, and finalization requires every reserved slot to be filled
(`:707–713`). All references therefore designate completed owned records.

SourceAnnotation.owner is now the same honest SourceRootId. Both root/local
annotations and expression ascriptions pass that owner unchanged into
`parse_annotation_with_marker`, which retains its actual position and type
(`source_annotation.rs:317–383`). Resolved SourceEffectIds/operation
declarations retain their original declaration identity; expression ownership
is not substituted for the effect family. Ordinary Act refusal and the empty
ordinary effect namespace are unchanged. In opt-in mode the original prepared
declarations remain the resolution environment.

All generalized handles expose source_root; definition-only accessors return
None for an expression (`module.rs:263–318`, `local_source.rs:47–77,299–309`).
No empty or artificial DefinitionRootId is synthesized. `owns_parameter`
retains its original narrow root-formal meaning; it need not return true for
inline/local parameters. Actual registered origins are available through
`parameter_source_origin`, and shadow consumers additionally require source
map membership and exact parse/binder checks (`shadow.rs:673–731`). Thus the
extended query does not authenticate an arbitrary ordinal under a valid root.

## 6. Original body occurrence and ordered new child identities

For every expression carrier, body is the initial slot0. `Builder::set`
reuses root.occurrence for that slot; the Definition branch remains unchanged.
Temporary IDs are private. Before publication, `order_occurrences(:101–133)`
groups all completed expressions by original source key, clears only the
stage occurrence map, and traverses plan.node.descendants in original preorder
(the pinned Rowan fact already established in the ordinary preservation proof).
Stable arena order breaks same-source-key ties. Its body branch again reuses
the original root occurrence; every other record obtains a checked next ID.
It rejects an unreachable source-key group rather than publishing it.

Let c be the cursor after every old binding carrier. For expression roots in
source order, every new nonbody occurrence is in the consecutive suffix
starting at c, independent of the temporary reverse-tail worklist order. Each
root body retains its earlier ordinary occurrence; it is not allocated from
that suffix. Forms, scopes, annotations and groups refer by root-owned indices
or identities, so remapping expression occurrence fields and the stage map
leaves no temporary occurrence reference elsewhere.

When ordinary lowering already recorded the root occurrence, `form_ordinary`
compares its old source key with the newly staged one and removes only that
duplicate from the stage (`:526–534`). In the actual ordinary/local-source
entrypoint, the only preexisting direct-root mapping comes from direct_atom
and lower_leaf: direct_atom accepts only a single IntegerLiteral or
IdentifierExpression child (`lib.rs:189–213`; `module.rs:2266–2303`). The
carrier's same no-tail descent sets slot0 at that identical child key. Thus
the check is met constructively; it is not an assumed root-origin equivalence.
If the ordinary Error had no root mapping, the authentic body mapping is added.
The ordinary expression and its occurrence are never replaced. The separate
shadow-application-only entrypoint does not run this expression carrier pass.

## 7. Staging, refusal, availability and source-order publication

`form_ordinary(:499–550)` takes the committed identity into a private local,
installs empty_stage, and passes only a private cursor into form. Its temporary
local-source grammar flag is restored before matching the result. The complete
mutable source cone is staged: occurrence/parameter/local/parameter-owner
maps; expression/binding/named-group arenas; annotations; lexical state; and
the local/parameter/group cursors. Builder operations do not mutate ordinary
items, errors, completed namespace or effect declarations. Annotation parsing
only borrows counters. `plain_binding_header` also only borrows counters.

Unsupported, Recovery or SupportedDepth drops all that private state, restores
the committed identity and returns only the actual root/key/reason. The
external occurrence cursor is untouched. The owning loop stores that outcome
and proceeds. Existing root-registry metadata survives a refusal because it
describes the genuine original Expression item, not a partially admitted
carrier. A refused root has no local_source_for result and no leaked local,
inline-parameter or child-occurrence source mapping.

Successful ordering precedes `append_stage`. `source_identity.rs:76–99` checks
parse-root equality, no overlap for every committed map lane, and empty staged
definition/expression-root maps. All four fallible reservations precede the
first extension. Only then are complete stage entries moved into committed
identity, the external cursor advanced and Supported returned. Different roots
have different authentic owners; checked fresh suffix IDs avoid occurrence
collision; root formal origins are not reinserted; the exact body duplicate
is removed as established in §6. These actual constructors meet the merge
checks, rather than merely assuming successful transactions preserve identity.

Availability propagates through the actual `?` caller and aborts the entire
unpublished module. A failure during ordering may drop the private saved
identity rather than restoring arbitrary retry state; the immediate-abort
caller does not retry or expose counters. This is publication safety, not a
general internal retry guarantee. No failed partial module becomes observable.
FormationError separates Unsupported from Availability at its actual owner
(`local_source.rs:24–39`); exhaustion/internal identity failures remain the
latter. This extension does not change those existing classifications.

Allocation order and outcome order differ deliberately. `module.rs:1169–1195`
reserves one optional slot per original plan, fills binding slots during the
first pass and expression slots during the second, then flattens slots in
their original order. There is exactly one fill per admitted ordinary binding
or expression and none for Error items. No sorting by new occurrence ordinal
is used. The final index maps each authentic owner to that unique source-order
position. Any failure before final HirModule construction publishes no module.

## 8. Ordinary and opt-in single ownership

The actual entrypoint flags are disjoint: ordinary uses
ordinary_source_carriers=true and local_source=false; the established opt-in
entrypoint uses local_source=true and ordinary_source_carriers=false
(`module.rs:989–1035`). The temporary flag inside form_ordinary does not reenter
lower_plan or change that phase choice.

Ordinary binding sources therefore live only in Supported outcomes; the
opt-in binding-source map is empty. Opt-in binding sources are still formed
exactly once at the old lower_plan site and inserted in local_sources
(`:1563–1580`); the ordinary binding outcome pass is skipped. Its complete old
loop, including old binding formation and ordinary identities, precedes the
new expression pass. Neither mode copies a binding source into the other
container. `local_source_for(:872–881)` first borrows a matching outcome and
otherwise uses the existing definition-only map fallback. Expression lookup
never falls back to a binding map. These are single-owned borrowing adapters,
not duplicate formation or reinterpretation of the old source.

The other existing opt-in source-identity/shadow-application entrypoints keep
their original modes and form no new carrier outcomes. They still acquire
authentic expression-root provenance without consuming IDs. This theorem
does not assume arbitrary private LoweringCounters flag combinations.

Thus the original G2 local conclusions follow at the actual frozen HIR
constructors for the full entrypoint domain. There is no source-qualified
counterexample in this derivation. Independent review and primary verification
must still establish acceptance of this artifact and the implementation gate.
G3/G4 and the original all-xi/z native semantic parent remain OPEN.

## 9. Frozen dependencies, evidence and commit packet

| Actual input | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/module.rs` | `2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e` |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` |
| `crates/yu-hir/src/module/source_annotation.rs` | `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f` |
| `crates/yu-hir/src/source_identity.rs` | `aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2` |
| `crates/yu-hir/src/lib.rs` | `5bdcb7c0df022da919cef5402c62dc1c7baf0700a4d06e526a608cbd7db21464` |
| `crates/yu-hir/src/shadow.rs` | `2dffd7fd6542eed9fd3346e0672e76197c248be9c84334f341c4d612234b7ee9` |
| Focused evidence only: `crates/yu-hir/tests/ordinary_expression_source_carrier.rs` | `693a14cb3678addbc6befc6486387b7c8f5c4a9011541b8bf9558467556b0ebc` |
| Governing module-expression design | `9a48f9ce4bee6e533cb0198d4112803dff927df71f5bca6bec084ced204dcd66` |
| Reviewed ordinary carrier preservation proof | `92eaf69e69b41b8f77ff68be7ee4b66a3e647e7920b039d97de71bb0c8c0fa1d` |

The focused test was read as correspondence evidence only: mixed roots,
duplicate/forward names, nested local/inline/Catch/annotation ownership,
foreign/child rejection, refusal and opt-in effectful construction. No theorem
is inferred from fixture count or a test pass. The primary owns checks.

Method: one bounded constructor/worklist and root-loop induction with exact
baseline diff inspection. Commands were bounded rg/sed/cat, read-only git diff
against the pinned baseline and SHA-256 reads; only this leased note was
written. No builds, tests, probes, network, Git mutations or delegation.
Allocation: 25-minute static packet; zero heavy processes or measured samples;
exact CPU/RAM/elapsed time uninstrumented. Requested normal Sol/high; observed
runtime model/effort metadata unavailable. Independent review pending.

Commit packet: sole path
`notes/theory/2026-10-16-module-expression-carrier-correspondence.md`, baseline
`1a64937f1`, exact dependencies above. Proposed checkpoint:
`research: derive actual module-expression HIR carrier correspondence`.
Shared-record proposal for primary/curator: record actual G2 authenticity,
ordinary/binding identity preservation, staged expression outcomes and opt-in
single ownership after independent review and HIR verification; leave receiver,
solver semantic and runtime bridges OPEN. No shared record was edited.

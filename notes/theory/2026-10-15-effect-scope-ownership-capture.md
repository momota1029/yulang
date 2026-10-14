# Effect-scope ownership through capture, aliases and returned functions

Date: 2026-10-15
Status: independently reviewed conditional structural derivation; original compose/source theorem OPEN
Baseline: `72e156f77d32efea98eeb06b3f54a98fdc9395c0`
Exclusive output: this file only; the earlier scoped-release note remains frozen
Authority: [compose scope decision](../design/2026-10-15-compose-scoped-effect-release.md), “Scope of the operation”; [inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md), §§1–3; [directional protection](../design/2026-10-06-directional-inferred-effect-protection-addendum.md), §§2–4.
Construction packet: primary-authorized reversible experiment using explicit source regions, an owned region forest at capture, and injective subtree cloning at fresh use. This note supplies a structural invariant; it does not adopt a new language rule or certify the experiment.
Review: M2 compiler_referee found no additional issue in this conditional derivation; native source guard and admission findings were repaired separately. The reviewed statement retains its explicit source/frontier/inventory hypotheses.

The [native checkpoint](../progress/2026-10-15-native-scoped-compose-experiment.md)
applies the scoped algebra to the actual identity route, records the discovered
extra-fiber admission counterexample and its owning repair, and distinguishes
the final three finite source observations from the still-open source theorem.

## 1. Frozen statement and hypotheses

The original parent still quantifies over the selected ordinary compose
source, compatible providers, the original complete Call witnesses and one
shared scoped assignment. It requires `'e` protection during passage through
`f`, scoped release also inside `'f`, preservation of independent scopes and
grants, natural inference and the required principality. That statement and
its source domain are not narrowed here.

The smaller statement is structural: explicit nominal ownership can be
copied through the existing capture/fresh-use phase without merging local
scope instances, renaming external instances, or losing the ownership boundary
of a returned callable. No numeric row level determines scope locality.

Fix a finite region forest `V` with an acyclic parent map. Different roots
have disjoint descendant sets. Each scope ID and each input-route ID has one
registered region owner; the two ID sorts remain distinct. IDs are nominal
instances, with original source provenance recorded separately. Let `F` be an
explicit finite antichain of capture roots, and write

```text
Owned(F) = union { Desc(root) : root in F }, including each root itself.
Local_F(id) iff owner(id) in Owned(F).
```

The owner supplies `F`. Neither `level > boundary`, row equality, successful
Function comparison, nor membership of an endpoint in a captured graph proves
that a scope binder is local. Whether the supplied forest binds exactly the
source-licensed scope instances is a separate constructor obligation.

Capture retains a finite scope-bearing payload `G`: transformer supports,
scope/tag references in latent Call qualifiers, original emission/release
descriptors, relevant future-consumer descriptors, and explicit per-provider
capture frontiers of returned Function values. Ordinary source identity,
attachment, provider, receipt, residual lineage and joint evidence fields are
retained independently; none is identified by the nominal scope map.

Require one of these inventory disciplines:

1. **Sealed inventory.** Each captured owned region has completed construction;
   every local scope/tag binder which a retained latent producer can later
   reference is included in the retained inventory. Delayed effect facts do
   not introduce previously unknown original local binders. Future generative
   source operations instead allocate in the corresponding cloned region.
2. **Persistent extension.** A retained per-use map can extend on later local
   references, always using the same cloned owner region, preserving earlier
   mappings, global freshness and the same use identity. Every future consumer
   uses that map. An ephemeral map dropped after restoration is insufficient.

The existing APIs do not establish either discipline for scope metadata yet.
The first is the smallest sufficient contract for the proposed source-owned
inventory. This is a hypothesis to implement, not a claim that a stored list
automatically captures complete future behavior.

## 2. Constructive clone

For caller construction region `C`, clone the captured owned region forest
by an injective fresh region map `kappa`. For each capture root `r`, attach
`kappa(r)` below `C`. For every nonroot `v` in `Owned(F)`, set

```text
parent(kappa(v)) = kappa(parent(v)).
```

Fresh images are disjoint from all old regions and from every other use's
images. Their original source-region provenance remains recorded. In
particular, the mapped roots are siblings under `C`, not one collapsed region.

For each local scope ID `s`, allocate one fresh scope ID `sigma(s)` with
`owner(sigma(s)) = kappa(owner(s))`. Do the same independently for input-route
IDs with map `iota`. Both maps are injective on their entire per-use local
inventory and fresh against old and externally retained IDs. On external IDs
they are identity. Thus the combined map is injective on local plus external
support. Cache each mapping once for the whole fresh use, across every context,
bound, qualifier, source descriptor and provider frontier. Never allocate a
new image independently while remapping each transformer.

Copy `G` structurally using these maps. Original source occurrence, original
provider identity and attachment lineage are provenance, so retain them; copy
their nominal region/scope/tag references consistently. Map every local
provider frontier through `kappa`; preserve a genuinely external frontier.
The existing type-row remap remains a separate Simple-sub operation, with its
own level/non-generic and intrusion rules.

## 3. Preservation and recapture derivation

**Ownership preservation.** Every copied local ID has the corresponding cloned
owner by allocation. Every external ID retains both ID and owner. Different
local IDs remain different by injectivity, and no local image equals an
external ID by global freshness. A scope and its release reference remain
equal exactly when their original IDs were equal. The same holds between an
input stamp and its ProtectBody guard.

**Ancestry preservation and reflection.** For owned regions `a,b`,

```text
a ancestor-of b iff kappa(a) ancestor-of kappa(b).
```

Forward direction follows by mapping the original parent chain. Conversely,
walk the cloned chain upward from `kappa(b)`. Within the cloned forest each
step is the image of the unique original parent. Crossing above a cloned root
reaches old `C`; it cannot reach another fresh cloned node through an old
ancestor because old parent pointers were not changed and no old region is a
fresh node's descendant. Thus a cloned ancestor `kappa(a)` lies on that chain
exactly when the original `a` lies on the original chain. Separate cloned roots
remain incomparable by the same argument.

**Returned-frontier equation.** Let `Q` be a retained antichain of provider
frontier roots contained in `Owned(F)`. Then

```text
Owned(kappa(Q)) intersect kappa(Owned(F)) = kappa(Owned(Q)).
```

This is ancestry preservation/reflection applied to each root of `Q`. No old
external ID becomes owned by the fresh frontier: its owner is an old region,
whereas all descendants of a cloned frontier inside this construction are
fresh cloned regions. At a later capture of that returned provider, precisely
the original `Q`-local IDs are therefore local again, and originally enclosing
IDs remain external to `kappa(Q)`. If later source construction adds children
below a cloned frontier, the same equation applies to the original copied
support; new IDs use their actual new owners.

**Alias closure.** An alias capture with an explicitly supplied frontier
reclassifies the same retained IDs by their actual registered owners. Another
fresh use performs the same injective clone construction. The two copies
compose: on a binder local to both captures, its image is `sigma2(sigma1(s))`;
on a binder external to the second, the second map fixes `sigma1(s)`.
Ancestry reflection proves these cases coincide with the retained original
frontiers. A scope's release and protection references follow the same case
because they use the same ID and maps. Thus alias copying does not require
reconstructing original scope ownership from type rows.

For a returned value with multiple callable provider arms, retain each
provider's original frontier and its existing joint witness. Do not choose
one frontier by row shape, or select provider/frontier witnesses separately.
The equation applies to each retained provider fiber; an explicit union forest
may be used only when the capture owner really binds that union. Introducing
per-Lambda region anchors can make anonymous returned frontiers expressible,
but does not by itself prove which provider frontier a joined result denotes.

**Transformer preservation.** The kernel's already derived alpha-equivariance
applies to `sigma,iota`, now justified as a single injective map over both
transformer support and incoming retained state. All stamps, conditional new
protections and releases therefore commute with this structural copy.
External active scopes are fixed and cannot collide with local images. This
is an application of the existing algebra, not another proof of it.

These are structural derivations under explicit fields and inventory
hypotheses. They prove neither the source's binder selection nor equivariance
of every native producer/consumer. Native constraint activation and complete
Call interpretation remain distinct obligations.

## 4. Why flattening and one-definition ownership are insufficient

The smallest flattening obstruction is nominal. Take outer region `R` and
child `Q`, scope `E` owned by `R`, scope `F` owned by `Q`, and a returned
provider with frontier `Q` referencing both scopes. An inner release must keep
its reference to external `E`, while its local `F` can freshen. Mapping both
owners to the caller's single region destroys that distinction; a later
capture cannot classify `E` external and `F` local from owners any longer.
For an external active `E`, renaming only its release reference would stop
that release from matching. This refutes the flattening representation
invariant. It is not asserted to be a parsed-source hygiene counterexample.

The native SCC driver first executes member schedules and routes internal
open uses, then captures each member's root. A member graph can consequently
refer to scopes constructed by another member. If those are source-bound
generic scope instances for the group, treating every other Definition region
as external is insufficient. The actual SCC capture owner must supply the
appropriate disjoint ownership forest/group. This is why the construction
accepts an antichain of roots, rather than assuming one root per definition.
No assertion that every sibling scope is always generic follows; that remains
the explicit SCC binding/capture contract.

Likewise, a local alias's capture boundary must be supplied by its source and
retained provider interface. Merely allocating a new local binding region
does not prove that all scopes reachable from its value become bound by that
alias. This note preserves whatever exact source frontier is supplied; it does
not silently add a new scope-generalization policy.

## 5. Actual owning API seams

At the pinned baseline the required fields are absent. The following are
implementation obligations for the reversible construction, not claims that
the APIs already meet them:

| Actual constructor/consumer | Required owned output or input |
| --- | --- |
| `candidate_source.rs::emit_candidate_source`, Work::Visit/Finish | Allocate/retain the active construction region for each original source occurrence; per-Lambda anchors are needed wherever a distinct returned-provider frontier must be represented. Preserve the current region across ordinary Apply/Group nodes. |
| Work::Initializer / Work::Install | Enter a distinct local initializer region, retain its parent and exact capture frontier, and seal its declared scope inventory at successful source publication. The already separate one-shot initializer effect stays outside the generalized value interface. |
| Original Call/upper-use construction | Allocate each scope/input tag once in its actual construction region. Retain the original qualifier and latent scope references even before any concrete contribution reaches a bound. |
| Action::Local / Action::Module | Supply the caller region from the original source occurrence. `DefinitionUse.parent` identifies only the containing definition and cannot distinguish nested initializer regions. An immutable occurrence-to-region map avoids reconstructing context on resume. |
| `candidate_scheme.rs::Graph` and `LocalScheme` | Retain the exact capture forest/frontiers, scope-bearing latent inventory and owner incidence alongside the existing row boundary. Type `Row.local` remains independent. |
| `capture_candidate_graph(row,boundary)` and inner capture loop | Accept the explicit forest and gather every retained scope/tag reference, including scope-bearing context roots and future Call qualifiers; the existing context payload traversal currently discovers weights only. A forest inventory can cover unactivated local qualifiers. |
| SCC capture loop / `route_candidate_graph` | Supply the authoritative group/member forest; preserve it when recapturing `stored.live_root`. Recomputing a live graph from the root does not reconstruct ownership. |
| `install_candidate_local_term` / `route_candidate_local_run` | Store the source capture frontier at installation, re-supply it for live recapture, and pass the current caller region into preparation. Open recursive initializer links remain on their selected monomorphic route. |
| `prepare_candidate_fresh_use` / `FreshUse` | Allocate one region clone and shared scope/tag maps before remapping any payload, using complete latent inventory. Retain them through every restoration step/pause, or eagerly remap every future producer descriptor before dropping them. |
| `candidate_context.rs::rename_fresh_contexts` | Remap scope-bearing operations and qualifiers through those same supplied maps, alongside the existing shared weight/context map. A separate fresh-ID allocation inside each transformer remap is incorrect. |
| `begin_candidate_fresh_bound` / restoration | Keep mapped qualifier, original source BoundKey, evidence antecedent and the same `context_use` jointly associated. A stored mapping alone does not prove later activation uses it. |

The current `prepare_candidate_fresh_use` row test is
`row.local && level > graph.boundary && !metadata.non_generic`. That is actual
type-row genericity; it supplies no region owner for a scope. Similarly,
`AnnotationScope` is existing source-name scope and is not automatically the
new construction-region or nominal-instance inventory.

These fields can be supplied at constructors without proving all source
semantics first. Their structural use has the derivation above. The source
argument that their exact forest/frontiers bind the intended scopes, and the
consumer correspondence for all relevant paths, remain necessary before
general hygiene or production claims.

## 6. Economy audit, stop condition and checks

Locality recovery from merged row levels is reconstruction debt: source
formation knows the active initializer/Lambda/SCC construction regions.
Retaining those owners and explicit frontiers removes that inverse problem.
Correct source binder selection, latent inventory completeness and replay
activation remain class A/B obligations; changing their representation does
not close them or weaken the original parent.

This packet stops at the constructive forest-clone contract and actual API
owners. The next action is to inspect the implementation's supplied fields
against §5, then independently review the structural correspondence. A missing
source frontier must return to its original constructor; do not substitute
another row-level classifier or silently treat a new forest as source authority.

No compiler changes, tests, builds, semantic probes, Git mutations, delegation
or external communication were performed by this producer. Checks are static
artifact whitespace/fences/links and dependency hashes. Requested runtime:
Sol/high; observed effective model/effort unavailable and recorded unknown.
The previous note was not changed. Original source/complete Call, scope
selection, recursive instances, all-path activation, termination, abnormal
publication safety, hygiene soundness and required principality remain OPEN.

Dependency SHA-256 snapshot before the region implementation:

```text
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd  crates/yu-solver/src/candidate_scheme.rs
9ba841ae93a8a732040d628cf184736613b27c85adc5f2a8a0db3b744e14c105  crates/yu-solver/src/candidate_source.rs
9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a  crates/yu-solver/src/candidate_scope.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461  crates/yu-solver/src/candidate_context.rs
5b6eb4660d2c72e1146d50bdb54318bf1f8e84faec42751f7ed38052587c1970  notes/theory/2026-10-15-compose-scoped-release-construction.md
```

## 7. Effect-only scope transport at the actual native constructors

This section pins the native constructor audit to commit
`72e156f77d32efea98eeb06b3f54a98fdc9395c0`, using its source independently of
the concurrent implementation. Its result is a native sort-preservation
argument and the exact scoped extension it supports. It does not claim that
the in-progress implementation has already installed or enforced that extension.

Keep three separate fields/responsibilities:

1. Ordinary `ContextExpr` retains its selected directed-weight interpretation,
   including the existing Function-port `Swap` operation.
2. A **deferred Value qualifier** retains original Call/demand scope/input-tag
   references and their source/provider fiber. It is not an executed
   `ScopeTransformer` on Value facts.
3. An executable `ScopeTransformer` acts on an Effect contribution route. Its
   only initial nonidentity introductions in this extension are actual
   ArgumentEffect/ResultEffect children and the selected Apply slot-2 outgoing
   release edge. Independent Effect transport/replay can retain/compose it.

The scoped invariant is:

```text
For every admitted Value relation, its executable scoped transformer is I.
Deferred Value qualifiers may be nonempty and remain separately retained.
```

All new Value relation/admission/transport APIs must explicitly enforce the
first line, including generic relation constructors and remapped contexts.
A nonidentity executable scope transform on Value is an internal invariant
violation; do not attempt to invert it or interpret it through the old
`ContextExpr::Swap`. This is an implementation-contract guard, not permission
to reject otherwise valid source programs. The constructor induction below
must explain why ordinary source generation cannot reach that violation.

### Constructor case induction

The induction is over actual relation/task generation, with source seeds as
the base case. At baseline the new scoped field does not exist; the extension
adds only the three Effect introductions above and the stated identity guard.
The following native owners establish the relevant kind cases:

| Native owner at the pinned source | Kind fact and scoped preservation step |
| --- | --- |
| `shadow_apply.rs::admit_candidate_fact`, source `admit_candidate_value_link`, `lib.rs::admit_lambda_fact` | Source Value links seed scoped I. Lambda entry/body and Apply slot-2 edges are explicitly Effect constraints; any selected operation is attached there, not to their owning Value construction. |
| `candidate_context.rs::candidate_context_pair` and `candidate_context_source` | Canonicalization matches Value→Value and Effect→Effect. The existing closed-allowance source context is selected only for Effect. New Value source scopes remain I independently of ordinary contexts. |
| `lib.rs` structural Function dispatch and `candidate_context.rs::candidate_function_port_admit` | A Value Function parent has scoped I by induction. Argument and Result children are Value and receive scoped I. ArgumentEffect and ResultEffect children are Effect; their actual directions are upper.AE→lower.AE and lower.RE→upper.RE. The deferred qualifier may introduce StampInput/PB only on those Effect children. The old ordinary Swap/Preserve context remains independent. |
| `candidate_extrusion.rs::candidate_apply_effect` | Inserts only `ExtrusionEndpoint::Effect` owners/bounds; its nonrow case delegates to the Effect operand checker. It cannot emit a Value bound. |
| `candidate_effect.rs::candidate_check_effect_operand` | Support/member expansion and symbolic-tail forwarding enqueue only `LiveConstraintTask::Effect`. The concrete allowance branch checks effect-family membership or forwards an Effect task; it never dispatches a Function Value. |
| `candidate_extrusion.rs::candidate_extrude` | An Effect endpoint visits Effect rows/views/tails. Only the Value Function case decomposes into Value, Effect, Effect, Value children. Hence extrusion can expose Value→Effect ports, but not carry an Effect route into a Value Function parent. |
| `candidate_extrusion.rs::candidate_insert_bound` and `candidate_context.rs::candidate_context_bound` | Actual bound constructors use matching owner/item sorts. A Value bound inherits I from its Value processing/origin case. Effect bounds may retain their Effect transform. Generic context helpers require the new guard; their unrestricted parameter types alone do not establish this invariant. |
| `candidate_extrusion.rs::candidate_replay_bound` and `candidate_step_bound_restoration_child` | Match `(Value,Value)` into a Value task and `(Effect,Effect)` into an Effect task; mixed endpoint sorts are unreachable in the actual owner rows. Replaying two Value bounds composes I with I. Effect replay may compose nonidentity scoped transforms. |
| `candidate_context.rs::candidate_context_transport_task`, `candidate_context_canonicalize_bounds`, and witnessed bound transport | Canonicalization changes representatives within the same typed endpoint sort. Extrusion/parent-copy bound transport retains that sort. Retaining/renaming a Value scope I leaves I; generic transport entrypoints require the new guard and matching source/destination kinds. |
| `candidate_scheme.rs::prepare_candidate_fresh_use` and `begin_candidate_fresh_bound` | Reconstruction follows `bound.kind` and the typed row/operand maps. It does not turn an Effect bound into Value. Injective scope/tag remapping preserves I, while deferred qualifiers use the shared ownership maps from §§2–3. |
| `candidate_context.rs` typed-drain/replay continuation owners | Store and resume the same `LiveConstraintTask` and relation. A pause changes neither sort nor transformer; resumed Function dispatch therefore still has the invariant it had before pausing. |

These cases close the kind induction for the inspected native owners under
the stated extension contract: no introduction of a nonidentity scoped
transform has a Value result, same-kind preservation cannot create one from
I, and the only cross-kind structural decomposition begins at a Value Function
and may introduce transforms only on its Effect children. There is no
Effect→Value producer among these native cases. An arbitrary private helper
call with mismatched kinds is not ruled out by its signature, which is why
the actual new Value APIs must enforce the invariant and implementation review
must cover their callers.

The scope qualifier must still reach the correct original Function comparison
jointly with its provider/source fiber. Value scope I does not prove qualifier
completeness, source alias propagation, correct output scope selection, or
activation; these remain the source/consumer bridge, not consequences of kind.

### Route-ordered replay, independent of arrival

At both `candidate_replay_bound` and the restoration child constructor, let
`owner` be the middle row and let `p` be the inserted bound's side. The actual
code chooses:

```text
positive insertion: lower=inserted, upper=existing opposite upper
negative insertion: lower=existing opposite lower, upper=inserted
```

It then sets `(lower_input,upper_input)` in that same orientation before
calling `candidate_context_begin_replay`. Thus the retained original inputs
always denote `lower_endpoint -> owner -> upper_endpoint`, regardless of
which bound arrived last. `candidate_context_begin_replay` separately reads
the lower and upper relation fibers and records both original BoundKeys in
`Dependency::Replay`; its new/new and old/new quadrants do not reverse those
roles. The derived scoped operation is therefore

```text
lower_transform.then(upper_transform).
```

Proof is induction on the replay derivation. A generating Effect edge has its
declared route operation. If the lower route's operation is `a` and the upper
route's operation is `b`, applying their actual route first visits the lower
then the upper constraint, so its state action is `b(a(state))`, represented
by `a.then(b)`. The retained orientation above establishes the induction
premise at the actual owner, rather than assuming a transition order in a
checker. Transport/renaming preserves that order. Associativity of the proved
kernel makes either replay bracketing agree on the same route, without
commuting different operations or identifying their witness fibers.

For Value replay, both scoped actions are I by the preceding kind induction.
At a subsequent Function comparison, its freshly projected AE/RE Effect
operations are therefore singleton introductions; there is no arbitrary
noninvertible inherited scope action requiring a contravariant Swap law.
After projection, ordinary Effect replay orders these operations along their
actual lower-to-upper routes.

This argument establishes orientation and sort feasibility. It does not show
that all bound-fiber pairs activate, that late qualifiers are completely
replayed, or that the resulting route is the complete source Call witness.
The scheduling theorem's separate two-sided activation hypothesis and the
original source gate remain OPEN. In particular, identity scoped Value
contexts remove the disputed inversion problem; they do not certify the
in-progress source integration.

Additional pinned constructor hashes, obtained directly with
`git show 72e156f77d32efea98eeb06b3f54a98fdc9395c0:<path> | sha256sum`:

```text
b73bcf9baa65c3e8c3093bb8ff6fa0e303fedb3baae35dc4587b70679991efee  crates/yu-solver/src/candidate_extrusion.rs
9eec4ecf8d7d5bb589c289edbbfc7b7c643124c9b6a4a8e3ae42f41fbe71344d  crates/yu-solver/src/lib.rs
c55a06c9bb6ac83e572240ede188a02a4ab17de0f4fe1b6212fb4490e32e321a  crates/yu-solver/src/candidate_effect.rs
```

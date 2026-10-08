# Proposed id-only SourceBuild owner and freeze boundary

Status: Draft / non-authoritative; implementation authority pending explicit user approval
Scope: production construction and retention of selected source records for the exact identity-function source `my id x=x`
Semantic change: none proposed; the selected source rules remain unchanged
Cutover: none; F5 continues to produce and consume the inference result
Baseline: `74c478aef`

## 1. Decision requested and boundary

This draft proposes one bounded source-construction gate: a new HIR-directed
source constructor would construct, validate, derive and freeze the selected
`SourceBuild` package and its `ScopedClosure` for the import-free, immutable,
unannotated identity-function source `my id x=x`. The frozen object is private
compiler metadata associated with the solved module. During this producer
gate, existing F5 remains the only inference route and does not consume the
metadata.

The proposed owner retains source facts at their source-owned construction
points. Existing HIR provides structural joins for definition/parameter/Name/
Lambda/component identity; the new constructor must form the original type
scope, inlet and invocation schema, fixed anchors, complete relation, source
FinalRoot and publication incidence. It derives the template set only from
the selected `Generalize_source` retain/fix walk over those typed records.
F5 Q/R facts, ordinals, levels and successful solving are not inputs to
construction or eligibility.

The exact decision for the user is whether to approve an id-only production
record-construction gate, which failure policy it may use, or whether to defer
production integration. Approval would authorize only the reviewed producer,
validation and private retention scope. It would not authorize a new inference
result consumer, public API, `cfg(test)` or feature-gated observer, changed
diagnostics, or F5 cutover. The design below keeps the failure-policy choices
explicit; it does not claim both unchanged behavior and mandatory metadata.

## 2. Governing source and preserved meaning

The [selected Source Generalize definition](2026-10-08-source-generalize-definition.md)
§§2–4 and its [construction/proof](../theory/2026-10-08-source-generalize-definition-and-proof.md)
§§2–5.2 already determine the native source records, their owning rules,
typed scopes, fixed-dependency walk, component relation and joint allocation.
The [uniform Value inlet](../theory/2026-10-08-uniform-value-entry-constructor.md)
§§4.1, 5.1–5.2 and 7.1 distinguishes the one ordinary parameter description
from its fixed generic raw inlet. The [id phase constructor](../theory/2026-10-08-id-public-phase-constructor.md)
§§2–5 retains receipt, Force, completion/pending/divergence, raw resumption,
formal rebind, Name/Result and future incidences.

This proposal adopts none of those meanings anew. For the exact source and
the genuine H-source premises, the selected constructor yields one ordinary
Parameter `Desc` for `x` at its pre-challenge type scope; the fixed generic
inlet has no free dependency on that description; body and outward payloads
reference the same declaration; and the final source root is the complete
synthesis root. The identity-instance [research crosswalk](../theory/2026-10-08-id-sourcebuild-instance-candidate.md)
records the precise premises and fields. The current compiler crosswalk is
conditional: existing HIR identities and F5 endpoints do not themselves
establish the selected semantic records or their local-law suppliers.

H-source and the proposed H-bridge remain separate. H-source is the selected
source constructors plus genuine L1–L5 local laws for this source. H-bridge is
the compiler-side proof that the emitted SourceBuild records are those exact
owning-rule outputs. Neither may be inferred from the other, from row equality,
or from solving success. An absent authentic supplier makes the artifact
ineligible for freezing; it does not permit filling the field with an opaque
success predicate.

## 3. Proposed source constructor and producer map

The production producer is a new private, HIR-directed selected-source
constructor over resolved HIR and the `SccPlan`. Its logical source records
must be formed from authentic source-owned inputs; their physical materialize,
validate and freeze point is unresolved. The current pre-session candidate
builds them before solver session construction. A second candidate builds
them at the final `finish` seam immediately before `SolvedModule` transfer.
Both consume already resolved branded records; neither reparses source,
inspects F5 rows, or evaluates runtime events. This constructor is proposed,
not an existing owner whose outputs can be extracted today. Its data output is
the selected source record graph plus origin references to the owning
HIR/component occurrences.
H-source and H-bridge are separate proof obligations for that output; they are
not runtime Boolean flags or presumed fields that certify themselves.

The current code supplies structural identities and a few joins. The exact
proposed owner boundary and its unsupplied semantic fields are:

| Fact | Current structural input | Proposed selected-source output and bridge obligation |
| --- | --- | --- |
| Shape/admission | `plain_binding_header` accepts an identifier and optional single identifier parameter; `HirBinding` retains visibility, parameters and resolved value; `SemanticImports` is empty for this standalone slice. | A preflight certificate for exactly one unannotated nonrecursive definition, one Value parameter, one body Name to that parameter, no import/capture and one complete source component. These shape facts do not certify immutable-world validity. |
| Definition, Parameter, Name, Lambda identities | `lower_module_with_counters`/`lower_plan` create the root and `HirParameterId`; `lower_leaf` resolves the Name to that parameter; `ConstraintBatch::collect_mode` retains recipe positions and `SccPlan` topology. | `H-identity` maps each branded occurrence to its authentic selected source introduction and exact parent/child incidence. A brand or ordinal is only a join key. |
| `d_a,sigma_a,Delta_a` and `T_id` | HIR retains parameter owner/name/range and lexical expression nesting/scope restoration. | The new Parameter source constructor emits one Value-endpoint declaration before the invocation challenge, its complete original dependency telescope, and the ordered source binder tree. Lexical depth or HIR ordinal cannot substitute for the source type scope. |
| `I_a, Intrinsic_q, U_g, IF0` | The Lambda recipe retains root/body/effect positions; no inlet schema is stored. | The new Parameter/Lambda source constructor emits the flexible description inlet and the fixed generic raw inlet as distinct typed outputs, including actual Pure/Value-entry role, ports and complete dependent incidences. The H-bridge must identify the selected ValueInlet and generic-inlet constructors. |
| `N_id` and invocation schema | Lambda admission currently emits an F5 Function bound; HIR carries the resolved Name body. | The source constructor emits the complete selected Name/Result/Call relation and finite invocation/event schema: receipt, Force, completion/pending/divergence, operation response and raw resumption, rebind, body and outward Return, and future scopes. Event operands remain bound variables in their original scopes; no runtime receipt or result is fabricated at construction. Every selected local law is a named bridge premise. |
| `anchors_id` and `C_id` | This exact HIR has no external Name/capture; collection and `SccPlan` retain singleton topology. `EvaluationClass::FetchValue` is only a value-shape classification. The selected [uniform Value-entry constructor](../theory/2026-10-08-uniform-value-entry-constructor.md) §5.1 independently forms one actual raw provider `U_g` at authentic unannotated Lambda formation, with source registration, Pure role for this projection, Value entry, formal `q`, source body operation, immutable capture references and `IF0`. | This common `U_g` formation permits either inert unevaluated publication or actual return/install of the same inert closure, as the identity instance §2.1 specifies. Authentic publication evidence must identify which anchor formation occurred and retain its complete fixed operands. The fixed generic inlet and original scope/lifetime fields remain part of `U_g`; the separate `Internal(C_id,r)` edge retains the full inferred relation. This is a selected semantic/source-side supplier, not a current Rust production field. The H-bridge must map the resolved HIR Lambda/Name and actual source registration to `U_g` and the actual publication/anchor formation, and L4 must still provide the valid initial-world and local registration laws. |
| `R_id` and FinalRoot | HIR root and definition-value root provide branded joins; F5 later selects a live row during generalization. | The selected FinalRoot constructor uses the complete unannotated synthesis root for this admitted source and emits its full source incidences before solving. It must not use the eventual F5 row as its semantic output. |
| `p_id` and source publication | HIR has a binding; scheme installation and terminal `SolvedModule` construction are separate solver events. | The selected source binding/publication constructor emits the semantic immutable binding-publication record and its incidence to `C_id` and `R_id`; `IdPublicationOwnerRef` must retain this actual event identity and its anchor-owner link. This source event is not scheme installation and not Rust result transfer. The local publication law and its owner are explicit H-bridge premises. |
| Freeze/storage | `InferenceSession` owns the solver batch; `finish` creates `SolvedModule` only after terminal finalization. | Two unresolved freeze placements: pre-session staging, where the package coexists with all later F5 work; or terminal construction after existing solve/finalization/counter snapshot, where the batch still owns structural HIR/component inputs. Neither placement supplies missing semantic owners. The late candidate must use an uncounted input path and add no later baseline allocation dependency. Storage/lifetime and failure policy require separate review. |

### 3.1 Concrete constructor contract for the identity source

The proposed constructor input is the resolved one-binding HIR shape and its
sealed singleton component join:

```text
IdInput = (root r, parameter q, resolved Name n -> q, Lambda ell,
           singleton nonrecursive component C_id, empty semantic imports,
           unannotated value-entry source form)
```

HIR supplies these as structural inputs: `lower_plan` creates the root and
Parameter and wraps the resolved Lambda; `lower_leaf` resolves `n` to `q`;
collection records the Lambda recipe; `SccPlan` seals component topology.
The admission check reads those branded records and rejects a mismatch before
metadata allocation. It does not use the parameter ordinal as a type
declaration, infer `Pure` from a solver row, or infer immutable-world validity
from the singleton SCC. `H-identity` is the source-to-HIR proof obligation for
this exact input tuple. The current structural locators are `SemanticImports`
and `plain_binding_header` in `crates/yu-hir/src/module.rs:106,2025`,
`HirBinding` in `:652–669`, root/Parameter/Lambda construction in
`lower_module_with_counters`/`lower_plan` at `:901–1358`, Name resolution in
`lower_leaf` at `:1966`, collection and `SccPlan` in
`crates/yu-solver/src/lib.rs:1137–1330`, and `LambdaRecipe` at `:697`.

The mathematical constructor contract is:

```text
ResolvedIdInput(r,q,n,ell,C_id,empty-imports,unannotated-value-form)
  + H-source(Parameter/Lambda/Name/Result/Value-entry, L1–L5)
  -> SourceBuildId(p_id,C_id,T_id,anchors_id,N_id,R_id,templates_id)
```

`H-source` is the authentic source-constructor/local-law premise defined in
§2, not a runtime Boolean argument or an opaque “success” field. The
constructor's case split must match the resolved shape to the selected
Parameter, generic Lambda/inlet, Name, Result, FinalRoot and binding
publication rules. `H-bridge` is the independent proof that the Rust case
split and emitted origin references implement that mathematical contract;
it is not established just by writing this signature.

Given the selected local constructor laws, the output contract is the concrete
instance in the [identity SourceBuild candidate](../theory/2026-10-08-id-sourcebuild-instance-candidate.md)
§§2–3:

```text
d_a = Desc(C_id,q,ValueEndpoint,sigma_a,Delta_a):a
intr_q = Intrinsic(q,source-slot,Value-entry,one-layer-port,original IF paths)
I_a = ValueInletSchema(q,a;Delta)
U_g = fixed generic raw closure over q, actual Pure role, Value-entry program,
      Name(n,q) body Result, empty captures and IF0
CarrierContract(U_g) = GenericValueInlet(q,IF0)
N_id = Build(S_id,T_id) with Parameter, Lambda, Name, Result and full
       invocation/event clauses
R_id = complete unannotated Lambda synthesis root
p_id = actual immutable binding publication selecting (C_id,R_id)
```

The scope/telescope order is fixed by the selected source rules, not HIR depth:
base world/registration/initializer anchors; `sigma_a` and `Delta_a`; the
description region and any `ViewLogic`; the independent complete inlet
challenge; event receipt; designated Force; `T_I`/Request/response/raw-resume
prefixes; only on Return, current world and `(v,p_v)`; formal rebind; `Name(n,q)`
and its body Result using that same decorated value/provider; invocation
Return; then hereditary future demands at the returned provider/port. Any
`Shared` binder stays once in the base, and each `EventProof` stays under its
actual event and original proof scope. No actual receipt, result or invocation
is evaluated while forming this finite schema.

`N_id` must retain the named clauses and incidences from the instance
candidate: Parameter declaration and complete `I_a/Delta/Intrinsic`; fixed
`U_g`/`GenericValueInlet`/`IF0` distinct from `Internal(C_id,r)`'s descriptions;
`PackGeneric` at a prechosen complete frame; same-frame Force elimination;
all Return, Request, raw-resumption and divergence alternatives; same-world
formal rebind; immutable Name restriction; body Result; original invocation
port projection; every guard and hereditary future obligation. Its `L1`–`L5`
inputs are exactly those listed in the candidate §3 table: independent
carrier/primitive laws when challenged (`L1`); authentic Parameter/Lambda/
Name/Result/Force/Bind constructors (`L2`); scoped same-value Name/Result
checking (`L3`); one valid immutable initial world and genuine closure/
registration formation (`L4`); and original response, raw-resume and future
compatibility/lifetime laws (`L5`). No literal primitive is introduced by
this source itself.

For this exact unannotated Lambda, the selected Uniform Value-entry rule
§5.1 is the source-side anchor constructor: it forms one actual raw provider
`U_g` before publication with its actual source registration, Pure role for
this projection, ordinary Value-entry program, formal `q`, body operation,
immutable capture references and `IF0`. The identity input's empty capture
premise does not choose the binding-formation arm. The identity instance §2.1
permits an inert unevaluated definition anchored by this source registration,
or an actual binding event returning/installing the same inert `U_g`; the
latter retains its actual `Executed`/`OneShot` and complete world/evidence
tuple. Both retain the separate `Internal(C_id,r)` description edge. Authentic
publication evidence must identify which formation occurred; no unevaluated
initializer premise or compiler execution is assumed here. The source rule
also states that `IF0` retains the original operational scope/lifetime fields.
The common source-side `U_g` formation does not make these records a current
compiler output. H-bridge must still map the HIR Lambda and resolved body Name
to this authentic `U_g` registration and the actual publication/anchor
formation, while L4 supplies its independent initial-world and registration
laws. Source publication remains a separate event selecting `R_id`; the
relation has no annotation/common-formation boundary for this input. No field
may be synthesized from F5 rows.

The typed output also carries origin references from every source-rule node,
binder and port back to its owning HIR/component occurrence. For this input,
root registration maps to `r`; the sole parameter construction to `q`; the
resolved body Name edge to `(n,q)`; the unannotated Lambda to `ell`; and the
sealed singleton source component to `C_id`. The source constructor, rather
than those structural records, introduces `sigma_a/Delta_a`, `I_a/IF0`, the
invocation/event schema, immutable-world/registration anchors, `R_id` and
`p_id`. The selected FinalRoot rule maps the complete unannotated synthesis
root to `R_id`; the source publication rule maps the actual immutable binding
publication to `p_id` and records its incidence to `(C_id,R_id)`.

These references are candidate compiler correspondence data. They do not
prove themselves: the constructor's checked pattern cases and the cited
L1–L5/local-rule lemmas must establish that no selected clause, guard,
dependency, binder or publication incidence is omitted. Until that H-bridge is
independently verified, the package cannot be frozen or used by a successor
consumer.

The source constructor assembles these outputs through the branded HIR and
component references, then runs the selected retain/fix walk over the complete
`N_id` and `R_id`. It must not reconstruct ownership from `F5cGeneralizer`, a
successful query, solver representatives, levels, row sharing, or numeric
row/binder ordinals. The table makes the proposed producer concrete while
leaving every absent local-law bridge visible; it does not establish that
those bridges already exist in production.

## 4. Record representation, validation and consumption

The logical private result is one immutable, collection-branded
`SourceBuildId` denoting `(p_id,C_id,T_id,anchors_id,N_id,R_id)` and its exact
retain/fix result. Under the compact §4.1 candidate, storage keeps only the
origin tuple and resolves the remaining fields through a complete fixed typed
`IdRuleSchema`. Under §4.2, the package instead retains a complete finite
variable-arity schema image with its actual source-owned counts. Neither
candidate stores runtime histories, copied source text or a separate
eligibility Boolean. `Desc` membership and fixedness are derived by the
selected typed walk. The complete relation, including constraints incident
to fixed anchors, remains attached through the chosen schema representation.

### 4.1 Compact representation candidate

For this id-only gate, the compact candidate is a fixed compiled
`IdRuleSchema` template plus one per-binding origin tuple, rather than
allocating a graph of runtime-history nodes:

```rust,ignore
#[repr(C)]
struct IdSourceOrigins {
    parameter: HirParameterId,
    name: HirOccurrenceId,
    lambda: HirOccurrenceId,
    component: SccComponentId,
    publication_owner: Arc<IdPublicationOwnerRecord>,
    final_root: IdFinalRootKind, // #[repr(u8)]
    publication: IdPublicationKind, // #[repr(u8)]
}

#[repr(u8)]
enum IdFinalRootKind { UnannotatedSynthesisRoot }
#[repr(u8)]
enum IdPublicationKind { ImmutableBinding }
```

The physical package is `IdSourceBuild { origins: IdSourceOrigins }`; it is the
stored identity for the logical `SourceBuildId`. The one fixed `IdRuleSchema`
is static program data. `IdSourceBuild::scoped_closure()` returns a borrowed
`ScopedClosureRef` over that schema and these origins; it does not allocate or
copy a per-module closure graph. The borrowed view cannot outlive its owning
`IdSourceBuild`.
The root is recovered through `parameter.definition_root()`; `final_root`
and `publication` identify the selected unannotated synthesis-root and unique
immutable-binding-publication constructors for this one-definition input. The
identity source has one eligible parameter, so no separate ordinal is needed.
`publication_owner` is a strong reference to the authentic immutable binding
publication record. Dereferencing it must identify actual `p_id`, its
`(C_id,R_id)` incidence and the binding/world owner's link to the selected
anchor formation. It must preserve that formation tag and every actual fixed
operand: for ReturnedInstallation, the selected
`Executed`/`OneShot` identity and complete same-world returned-provider /
evidence tuple; for inert registration, the actual closure/delay registration
and fixed capture environment. A schema tag or fresh schema variables cannot
recover those values or event identity `p_id`. The reference is only
representationally sufficient if the publication/anchor-owner record and its
transitive dependencies outlive the package and remain immutable; neither an
owner type nor a current production supplier has been identified. The fixed
compiled `IdRuleSchema` refers to origin slots for `root`, `q`, `n`, `ell`,
`C`, `p_id` and the anchor-owner output; its binder tree and `N_id` clauses
are the complete §3.1 graph. Static schema code is shared across all
instances; it must not expand runtime histories or omit any rule node. A
direct owned-graph representation is the comparison case and would copy each
node/binder/clause/edge into per-module storage. The static-template candidate
adds slot resolution whose completeness and cost must be reviewed. This
representation is a candidate, not an implementation or approved choice.

One concrete ownership candidate, still unreviewed as a complete architecture,
uses separate immutable records and a single owning direction:

```rust,ignore
struct IdPublicationOwnerRecord {
    binding_root: DefinitionRootId,    // join key; not p_id by itself
    component: SourceComponentRef,     // authentic C_id
    final_root: SourceFinalRootRef,    // authentic R_id
    anchor: Arc<IdAnchorFormationRecord>,
}

enum IdAnchorFormationRecord {
    InertRegistration { /* U_g source registration, IF0 and full fixed operands */ },
    ReturnedInstallation { /* same U_g, actual Executed/OneShot and full world/evidence tuple */ },
}
```

Both arms remain permitted for the exact identity input under the identity
instance §2.1. Uniform Value-entry §5.1 supplies their common `U_g` formation;
authentic publication evidence must select the actual arm. That choice remains
open until its source owner and complete fixed operands are identified.

These names are proposed types, not existing Rust definitions. The outer
`publication_owner` slot is `Arc<IdPublicationOwnerRecord>` in this candidate.
Its allocation identity plus this typed immutable-binding record represents
`p_id`; `binding_root` supplies the branded HIR join. The root alone is not
a publication event. Before using this encoding, the new source constructor
must prove a bijection for this exact one-binding slice: one admitted binding
has exactly one relevant immutable source publication, and that publication
selects the recorded `(C_id,R_id)`. It must not conflate publication with
registration, RHS execution, scheme installation or terminal result transfer.
This source-to-HIR bijection is currently unproved. The anchor record is formed
by its own authentic source rule and then linked from publication. This displayed
two-record shape has no direct owning back-edge. The complete transitive
strong-reference graph must also be acyclic; the placeholder dependency types
do not prove that condition. Every record must retain complete dependent
operands, not only IDs or tags.
This separates event identity from formation identity and does not conflate
publication with `Executed`. The typed owners and their current compiler
suppliers remain unimplemented and unidentified.

The fixed-template candidate is not yet complete: the governing sources do
not give the concrete occurrence cardinalities or telescope arities needed to
instantiate `IdRuleSchema`. A semantically compatible alternative is a
finite, variable-arity schema image supplied by the authentic source owners;
the next section specifies that candidate without treating unknown operands
as empty.

### 4.2 Parametric finite-schema candidate

The selected Source Generalize construction permits finite local rule
catalogues whose alternatives carry their actual operand telescopes. It does
not require one global integer arity for `Delta_a`, IF0, or event/proof
regions. A second representation candidate retains the authentic finite
schema image with its actual lengths and incidences, instead of assuming a
compiled fixed-cardinality `IdRuleSchema`:

```text
IdSchemaImage = (
  typed source-owner records,
  ordered scope/binder records,
  ordered dependent telescope slots,
  rule-constructor alternatives and premise occurrences,
  classified field incidences,
  registered typed-reference targets
)
```

This is a proposed storage boundary, not an existing compiler type. Each
Parameter/Lambda/invocation/final-root/publication owner must provide the
complete immutable data for its actual alternatives. A telescope slot records
its sort, owning source constructor, original scope, and permitted preceding
dependencies; an incidence points to a typed target and retains that target's
full dependent telescope. `Delta_a`, complete `Delta`, `Intrinsic`, IF0,
`EventField`, and `EventProof` remain distinct typed inputs. A `RuleRef` may
avoid copying a registered target only if it preserves the target's full
schema and dependencies. References cannot become opaque predicates or
successful-query facts.

The seven `IdSourceOrigins` fields remain one-binding join inputs; the
reachable schema image has variable lengths. SourceBuild validation must
reconstruct the same clauses/alternatives and binder tree from this image,
then run the selected retain/fix walk. It must retain the full
`Internal(C_id,r)` relation, preserve the separate actual anchor owner, and
derive the same one-template result only under H-source. It must not expand
future histories into package data. A canonical convention for conjunction
and union storage, scope-parent links, sharing/deduplication, and typed
reference resolution is still required before implementation; neither the
source semantics nor this sketch selects those representation details.

Let `N` be schema nodes, `E` all classified dependency, premise, and reference
incidences, `B` scope/binder records, `T` telescope slots, `R` registered
references, `O` unique transitive owner allocations, and `P` their retained
dependent payload. These are measured from one complete frozen owner image;
they are not fixed constants or assumed small. No validation-time or scratch
bound is selected yet. A later bound must name the concrete passes and work
units, show that target lookup and deduplication have bounded cost, and account
for scope legality without repeated ancestry walks. It must also state the
maximum worklist occupancy and whether reconstructed clauses/incidences are
materialized. Counting telescope slots alone does not bound their dependency
incidences. Structural retained cost must separately account for array
capacities/layouts, `O`, and `P`; peak cost must include the staging image and
validation scratch while F5's batch is live. No fixed byte total or linear
validation claim follows before owner types, normalization, capacities,
algorithms, and transitive ownership are supplied.

This variable-schema candidate preserves the selected source relation only
when each authentic owner emits all alternatives and original scopes. It
does not itself supply `Delta_a`, any L1–L5 law, H-identity/H-bridge, the
publication/anchor event, or a failure policy. It may avoid a fixed census
requirement, but still needs independent review of preservation, resource
accounting, ownership/lifetime and production correspondence. Adopting this
internal representation is a new architecture decision and requires explicit
user approval before implementation.

### 3.2 Bounded current-production owner audit

A refreshed read-only audit at the pinned production source found branded
structural joins but no current authentic publication/anchor owner for this
package. The scope is the ordinary HIR collection, Lambda admission, SCC
planning and terminal `SolvedModule` path; this is not a global absence claim.

| Required field | Current evidence and status |
| --- | --- |
| `r/q/n/ell` | Structural identities exist: `DefinitionRootId` and `HirParameterId` in `crates/yu-hir/src/module.rs:185,271`; resolved Lambda at `:1339`; the collection Parameter/recipe join in `crates/yu-solver/src/lib.rs:1153`. Their semantic-introduction correspondence remains H-identity. |
| `p_id` | No immutable source-publication event exists in the inspected chain. `HirBinding` is constructed at `module.rs:1349`; scheme installation at `lib.rs:14166` and Rust result transfer at `:15970` are different events. |
| `(C_id,R_id)` | Only structural joins exist: `CollectedDefinition` at `lib.rs:510`, `SccPlan` at `:1330`, component membership lookup in `crates/yu-solver/src/scc.rs:689`, and root-row lookup at `lib.rs:15490`. None selects a complete source `R_id` in a publication record. |
| Counted owner queries | `ConstraintBatch` exposes definition/component accessors and a probe snapshot (`lib.rs:1434–1538`); a private sealed-plan accessor exists at `:1969`. Several apparently read-only accessors increment Arc-backed atomic counters, and `ConstraintBatch::clone` shares those probes. A producer cannot infer counter neutrality from `&self` or from cloning; the exact constructor input path must use an inspected uncounted accessor or explicitly account for the counter change. |
| Inert Lambda anchor | `ResolvedExpr::Lambda` at `module.rs:461`, `LambdaRecipe` at `lib.rs:697` and construction at `:1766`, and Function fact admission at `:10790` provide shape/recipe data. They do not retain raw provider, role, Value-entry/IF0, port, world/allocation/lifetime operands or owner-certified captures. `FetchValue` (`module.rs:438,644`) is not such evidence. |
| Inert Delay anchor | No Delay variant appears in the inspected ordinary HIR expression inventory (`module.rs:443` onward). No authentic Delay registration supplier was found in this bounded path. |
| ReturnedInstallation | No actual binding event `b`, selected arm, `Executed`/`OneShot` identities or returned provider/same-world evidence tuple appears. `AdmissionReceipt` at `lib.rs:3023` is store-transaction provenance, not source execution. Lambda admission builds type terms (`:10798–10820`) but does not execute an initializer. |
| Terminal lifetime | `ConstraintBatch` owns HIR and collection structures (`lib.rs:796`); `InferenceSession` owns the batch (`:7419`). `finish` transfers HIR, schemes, arena, provenance and store into `SolvedModule` (`:15970–15986`; fields at `:7333`), but not the SCC plan, collected-definition records, Parameter recipes or Lambda recipes. There is currently no owner payload to retain. |

Therefore direct Arc ownership is only a candidate retention mechanism: it
cannot create the missing source publication, formation or local-law outputs.
A bounded architecture assessment found that the new source constructor may
conditionally reuse `DefinitionRootId` as the publication's branded join key
for this exact one-binding slice, paired with the typed
`IdPublicationOwnerRecord` identity. The selected source definition requires
an authentic event, not a newly minted numeric ID. But Source Generalize
distinguishes member export from joint tuple export, so the constructor must
prove exactly one relevant publication per admitted binding and its selection
of full `(C_id,R_id)`. This could avoid a separate event-ID allocation; it does
not remove the owner-record allocation or supply the event semantics by itself.
The current compiler still has no such constructor/bijection. The next
correspondence evidence must identify an actual permitted anchor formation and
its authentic owner, prove the restricted publication bijection and selected
root, then trace both payloads through staging and terminal retention. A
package built only from HIR origins, `FetchValue`, F5 rows, a scheme-install
notification or a schema tag cannot distinguish otherwise identical
structural inputs with different actual formation/event/world evidence and
fails H-bridge.

The minimum anchor-owner payload contract is:

| Formation | Actual retained owner fields | Required relation/lifetime |
| --- | --- | --- |
| Inert registration | Authentic closure/delay registration; actual role, entry/code and port; fixed capture environment, including owner-certified emptiness; immutable world, allocation and lifetime operands; its dependent generic inlet/IF0 registration. | `publication_owner` resolves to actual `p_id` and its link to the original Lambda/Delay and binding-world owner. Any `Shared` witness stays at its one original binder. |
| Returned installation | Actual binding event `b`, selected arm, `Executed` and `OneShot` identities, returned provider, and complete same-world return/world/allocation/installed-contract/evidence tuple. | `publication_owner` resolves to `p_id`, its `(C_id,R_id)` incidence and the actual anchor event. Every dependent field remains reachable and fixed. The separate `Internal(C_id,r)` description edge stays distinct from fixed `Established`/`OneShot` contract dependencies. |

The publication/anchor owner and all transitive dependencies must remain
immutable and alive from SourceBuild materialization through terminal transfer
and for the complete package lifetime. Under pre-session staging, that
includes F5 batch/session coexistence; under terminal materialization, it
begins after successful F5 completion. An Arc-shaped handle alone
proves neither payload completeness nor this lifetime relation. The tuple
estimate below includes only the reference field, not this owner record, its
dependent graph or any separately retained allocation.

On a 64-bit target, the current field definitions give a structural estimate
for the tuple: `HirParameterId` is 24 bytes (two Arc pointers in
`DefinitionRootId`, one `u32`, alignment); each `HirOccurrenceId` is 16 bytes
(one Arc pointer and one `u32`); `SccComponentId` is 16 bytes (one Arc pointer
and one `u32`). A direct `Arc<IdPublicationOwnerRecord>` would contribute one
pointer (8 bytes); the two one-byte tags then yield a conditional 88-byte
`#[repr(C)]` estimate after alignment. A branded Arc-plus-`u32` handle (16
bytes) would instead yield 96 bytes. These are alternative proposed handle
layouts, neither a current production type. `IdSourceBuild` has no additional
fields beyond the tuple. The estimate excludes owner records, Arc control
blocks, complete dependent payload, allocator overhead and separately
retained allocations. These are structural calculations, not a measured or
compiler-verified `size_of`.

Storing `Vec<IdSourceBuild>` in `SolvedModule` adds a 24-byte vector header to
every result on the same target. Empty/nonapplicable results allocate no
payload. One admitted identity source stores one estimated 88-byte tuple with
the direct Arc candidate or 96 bytes with the branded-handle alternative;
the retained owner record and its dependent fields are not included, so this
is not yet a complete per-element bound. The `ScopedClosureRef` is borrowed on demand and adds no
per-module heap allocation; its stack layout is not included. Construction is
once per admitted binding/module. Under pre-session staging, the complete
package coexists with the F5 session until terminal transfer, where the vector
can move into `SolvedModule` without copying. Under terminal materialization,
construction happens after the existing F5 finalization and feature-gated
capture-position collection, immediately before result transfer; the complete
package then moves into `SolvedModule`. That candidate requires every needed
authentic input to remain available there and must not displace any later
baseline allocation. The schema template has no
per-module heap allocation, though its static/code footprint and exact
binder/clause/edge counts still need an explicit manifest. A direct owned-graph
option would add its exact node count, arena/vector headers, capacity slack and
allocator overhead instead. This candidate narrows runtime storage accounting
but does not close publication/anchor-owner payload cost (including separate
Arc control blocks and allocation capacities), vector capacity/allocator cost,
static-schema cardinalities, total binary size, architecture-specific layout,
or the source/anchor decision.

The source constructor emits `R_id` and `p_id` itself from the selected
FinalRoot and source-publication rules; it does not wait for a later F5 scheme
installation or terminal Rust result as a semantic supplier. At the selected
placement, it stages the complete graph, verifies every field and
cross-reference, runs retain/fix, and returns either one immutable
`IdSourceBuild`/`SourceBuildId` whose borrowed `ScopedClosureRef` is complete,
or an explicit no-package result. The closure view is reconstructed from the
static schema and package origins without a per-module graph allocation. No
partial package transfers. Structural
`NotApplicable`, a missing selected local-law supplier, an internal
cross-reference defect, and catchable allocation failure are distinct
outcomes; §5 gives the unresolved policy choices. Terminal transfer to
`SolvedModule` happens only after the existing F5 session reaches successful
finish.

The package is retained in private per-module compiler storage as a future
successor-consumer input. For this first gate, F5 does not read or alter it and
still owns inference, solving, public projections, diagnostics and returned
results. The package is not an alternate acceptance oracle or a user-visible
mode. Its freeze does not prove that later F5 consumers preserve its rules.

## 5. Resource and failure contract

This exact producer gate admits only one definition, one ordinary value
Parameter, one resolved body Name to that Parameter, one unannotated Lambda,
one final synthesis root, no recursive peer, no capture/import, and no
annotation/conversion. For a fixed compiled template, node/edge/scope/telescope
counts are constant only after its complete source schema is supplied. For the
parametric candidate, those counts vary with the authentic finite owner image;
validation must account for its actual incidences and dependent telescope
slots. Either representation must have a bounded walk over its supplied
schema and resolved HIR/component records, with no history expansion. This
does not bound the publication/anchor owners' transitive dependency closure:
world, allocation, installed contract, evidence and lifetime references may
retain owner data whose size scales with the source environment. The package
stores typed source records and references, not cloned source text or solver
arenas. A later extension to general lambdas, imports, State, recursive groups
or arbitrary operators requires a new structural and resource review.

Construction is attempted at most once per admitted binding/module, at the
selected placement. The selected shape is a structural
preflight; an input outside it is `NotApplicable` before allocation. A missing
local-law supplier is an incomplete SourceBuild premise, not malformed source
and not resource exhaustion. A stale brand, duplicate owner, omitted required
clause or failed postcondition is an internal invariant defect. A fallible
reservation error is a catchable metadata-allocation failure. These cases
must not be collapsed into one error.

Two production policies remain possible and neither is selected here:

1. **Optional sidecar while F5 remains authoritative.** For structural
   `NotApplicable`, missing supplier, or catchable metadata-allocation
   failure, discard the entire isolated staging area, record no certified
   package, and continue the unchanged F5 route. A future consumer must treat
   absence as “no SourceBuild evidence” and cannot use partial fields. An
   internal invariant defect can either be surfaced as a compiler defect or
   discard only the sidecar. Discard-only avoids a new metadata error. With
   pre-session staging, a successfully built package increases live storage
   during F5 startup and solving, so an F5 reservation may fail in a state
   where it succeeds without the sidecar. With terminal materialization, the
   candidate is built only after successful F5 finalization and optional
   capture-position collection; on metadata failure it must be discarded and
   the successful F5 result returned unchanged. This still does not establish
   process-level allocator equivalence or equal availability for later
   consumers. The unchanged-F5 claim can
   cover semantic inputs, F5 facts, schemes, diagnostics, provenance and
   counters for runs where F5 completes, subject to an uncounted construction
   path. Exact availability equivalence under memory pressure is an unresolved
   resource-boundary decision; isolation alone does not prove it. Surfacing an
   invariant defect changes the result contract and requires explicit
   approval. Every catchable metadata allocation must be fallible for a
   recoverable sidecar outcome. The design cannot promise recovery from
   process-aborting OOM.
2. **Required metadata for the admitted shape.** Missing suppliers,
   internal defects and allocation failure prevent a successful result for an
   otherwise F5-solvable input. This changes the resource/failure boundary
   and needs explicit approval under `rules/design-authority.md`; it cannot
   be described as unchanged acceptance or resource behavior.

Deferring production integration is also available until the producer,
representation and consumer plan are complete. It adds no production
failure path. The existing solver consumes its batch in `SolvedModule::solve`
and only constructs `Ok(SolvedModule { .. })` in `finish`; it does not restore
a caller-owned live session after an error. Therefore a post-solve SourceBuild
failure cannot be called a rollback to a resumable F5 solve. Under an optional
sidecar proposal, either build isolated metadata before the F5 session or
materialize it immediately before `SolvedModule` transfer; each placement must
transfer only a complete package or explicit absence. Terminal materialization
must return the completed baseline result if SourceBuild construction fails.
Under required metadata, the exact failure point and observed result must
instead be approved.

Both placements create a counter-isolation obligation.
`ConstraintBatch` accessors that appear read-only can increment Arc-backed
atomic probes, and cloning the batch shares those probes. A SourceBuild
constructor must use a concrete uncounted sealed-plan/input path if unchanged
F5 counters are claimed; a borrowed receiver or private clone alone is not
evidence of counter neutrality. Terminal materialization must not call a
counter-mutating accessor after the existing snapshot. No complete constructor
path is selected here.

For resource accounting, compare unique live storage regions with and without
the sidecar at each phase. `bytes(S)` counts each live heap-allocation layout
and each in-object field range once; it includes requested capacities and
inline object size, but not allocator metadata or process RSS. Let `B(t)` be
the unchanged F5 pipeline's live storage set at phase `t`: it includes the
HIR, collected batch/SCC plan, live `InferenceSession`, and every finish
output/local allocation that remains live, even while its owner moves. Let
`A_new(t)` be new publication/anchor-owner records and their transitive
dependency allocations, `A_keep(t)` pre-existing publication/anchor-owner and
transitive dependency allocations that are live only because the sidecar
extends their lifetime beyond the unchanged pipeline's baseline lifetime at
phase `t`,
`M(t)` all sidecar-owned storage live at phase `t`: origin records, schema,
scope/binder, telescope and incidence buffers at their actual capacities,
including vector headers, and `V(t)` sidecar-only construction/validation
scratch. Define those added sets disjoint from `B(t)` and from each other; a
target still live in `B(t)` is not also in `A_keep(t)`, and shared Arc targets
are counted once by allocation identity. The borrowed `ScopedClosureRef`
contributes no heap allocation.

```text
pre-session construction peak:
  bytes(B(pre) ∪ A_new(pre) ∪ A_keep(pre) ∪ M(pre) ∪ V(pre))
F5 run coexistence at t:
  bytes(B(run,t) ∪ A_new(t) ∪ A_keep(t) ∪ M(t))
finish coexistence at t:
  bytes(B(finish,t) ∪ A_new(t) ∪ A_keep(t) ∪ M(t))
terminal retained increment:
  bytes(M(final) ∪ A_new(final) ∪ A_keep(final))
```

For pre-session staging, the finish baseline set includes F5 result
allocations that coexist with session locals before transfer; moving a field
changes its owner, not its live bytes. In that candidate, `V(t)` is zero after
validation before session startup. Its peak is the maximum over every instant
of pre-session construction, F5 run, and finish, including temporary
old-plus-new buffers during reallocation or replacement.

For terminal materialization, the separate finish peak is:

```text
terminal construction peak at t:
  bytes(B(finish,t) ∪ A_new(t) ∪ A_keep(t) ∪ M(t) ∪ V(t))
terminal retained increment after transfer:
  bytes(M(final) ∪ A_new(final) ∪ A_keep(final))
```

Here `B(finish,t)` includes all still-live baseline session and result storage
at the proposed seam; `V(t)` includes late constructor and validation scratch.
This candidate avoids competition with prior F5 allocations only if no
subsequent baseline allocation depends on the same resources and all authentic
inputs are available without counter-mutating accessors. A failed optional
construction must release all candidate-only storage and return the successful
baseline result. It does not prove equal process-level availability or future
consumer resource behavior. Both candidates' peaks are phase-set definitions,
not completed numeric bounds.

The selected owner type must determine `A_new`, retention analysis must
determine `A_keep`, the validator must expose `V`, and vector capacity
determines `M`. A constructor-by-constructor table must identify each record,
buffer and index allocation, whether it is fallible, and how its failure is
handled under the selected policy; `try_reserve` alone does not make later
`Arc::new` or nested allocations recoverable. The design must also bound
failure-discard and terminal-drop depth, or provide a reviewed teardown
strategy. The existing `ConstraintBatch` is live before session startup
and is therefore included in `B(pre)`, rather than omitted from construction
peak. The tuple estimate is only the per-element logical payload component
of `M`, not a substitute for this phase accounting. No such allocation manifest
exists yet. Static layout/accounting comes before measurement; if the selected
owner cannot bound retained/peak storage, request focused measurement under
`rules/performance.md`. No cap is inferred from F5 Q/R lanes.

For the parametric candidate, approval requires a complete frozen schema
instance to expose its actual `N/E/B/T/R` counts, exact chosen Rust layouts
and capacities, transitive owner allocations/payloads and validator scratch.
The design must also state a structural size envelope for admitted schema
images, or explicitly present a deterministic limit and its behavior for
approval. It does not need one global node/edge/telescope integer if lengths
are authentic source-owned data. No such size envelope or limit is selected
here. If the final representation instead chooses a fixed compiled template,
that template must provide an exact full occurrence/telescope manifest.
Focused measurements may validate a bounded static account but cannot
substitute for missing source owners or an undefined admitted-size envelope.
No timing campaign is planned unless static call-frequency/complexity
analysis leaves a concrete decision unresolved.

## 6. Atomicity and non-goals

Any transferred source package is complete and immutable; partial records
never enter `SolvedModule`. The F5 branch remains the only inference
implementation during this gate. Under the optional sidecar policy, metadata
failures can be hidden from the ordinary result only when the entire sidecar
is discarded and F5 completes. The added retained bytes can still change F5
availability under memory pressure, so identical acceptance is not established
by this policy. Surfacing an invariant mismatch as a compiler error, or
requiring metadata for a successful result, changes the failure contract and
needs explicit approval before implementation. Neither policy promises
recovery from process-level OOM. Deferring production integration has no new
failure path.

Not authorized by this gate:

- Make the F5 solver, generalizer, closed-scheme storage or use routers consume
  `SourceBuildId`/`ScopedClosure`.
- Replace `ClosedValueScheme`, public/root projections or feature-gated F5
  observation APIs.
- Change Apply ownership, source constructor families, annotations, recursive
  interfaces, handler/effect semantics, imports or principality.
- Claim whole-language source coverage, L1–L5 validity, transformed-public
  consumer correspondence, fresh-use/lifecycle correctness, or F5 cutover.
- Add a test hook, a public API, or behavior-specific fallback.
- Treat metadata absence as evidence that a source is invalid or unsupported.

The subsequent consumer gate must design effective solving of the retained
joint relation, independent-use and alias allocation, designated transformed
public export, actual public/root/occurrence projections, diagnostics and
atomic `SolvedModule` publication. It requires its own reviewed authority;
this id-only record producer does not settle it.

## 7. Review, verification and approval gate

Classification: new internal compiler architecture with hot-path allocation
and source ownership/publication risk; proposed M3 review. Required
independent reviewers are `compiler_referee` for ownership, scopes, supplier
validity and atomic publication; `spec_auditor` for exact Source Generalize
conformance and gate boundaries; and `performance_auditor` for record-size,
construction-work and retention risk if static accounting remains materially
uncertain. Convergence requires no unresolved blocking/major finding and no
unowned source field.

No code, tests, builds or measurements were performed for this draft. Before
implementation, obtain explicit user approval of the reviewed producer scope,
representation and selected failure policy. Implementation would be limited
to the private SourceBuild producer/storage and the approved complete-or-absent
transfer; the existing F5 consumer remains authoritative. Existing question
`flat-application-owner-family` remains independent and unanswered.

## 8. Open design obligations

1. Fix the exact Rust output representation and report structural counts,
   bytes, construction frequency, and peak/retained coexistence with F5.
2. Identify each local-law/source-owner supplier and prove its output joins
   the retained HIR identities. `H-bridge` remains open until this is
   established; structural locators alone do not supply semantic records.
3. Select an approved failure policy, including the disposition for internal
   invariant defects and process-level allocation failure.
4. Validate complete-or-absent staging and terminal `SolvedModule` transfer;
   ensure an optional sidecar cannot alter F5 facts, results or diagnostics.
5. Review retention lifetime for the private graph; any later consumer
   migration gets its own reviewed implementation gate.

These obligations are part of the review packet, not assumptions that the
implementation can resolve by choosing convenient owners. If review shows
that the object cannot be retained without changing result behavior or
resource acceptance, return to design before implementation.

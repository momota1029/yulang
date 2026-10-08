# Identity SourceBuild: production supplier and H-bridge audit

Status: Research evidence only; non-authoritative; no implementation or semantic approval
Date: 2026-10-08
Method: Bounded source-to-implementation correspondence audit
Packet baseline: `research/simple-sub-intrusion`, HEAD `8f2c5a8e2`
Reviewed draft: `notes/design/2026-10-08-id-sourcebuild-owner-design.md`
Reviewed draft SHA-256: `785a5a4d5133d8c1790e1e0a5f85f19bab83e0d0c84c502951ab6f80f1596bca`
Scope: ordinary identity binding `my id x=x`; selected records described by draft §§2–4

## Finding

The inspected production path supplies authentic **structural identities and
joins** for the definition, sole parameter, resolved body Name, wrapper Lambda,
and collected component recipe. It does not supply the proposed source semantic
records. The draft correctly identifies its selected-source constructor as a
new producer; this audit supplies no evidence that those semantic outputs can
instead be extracted from the current Rust owners.

In particular, a type-row parameter, an empty-effect constraint, a Function
bound, a frozen SCC, a scheme-install event, and successful terminal transfer
each have a real current owner. Their owner domains differ from the proposed
description scope, generic inlet, source invocation, immutable world,
publication event, and complete source root. Reusing their identities as joins
does not establish H-bridge. No semantic field should be recovered from F5
rows or successful solving.

The rule selected by the mathematical proposal can serve as a candidate
specification for a new source constructor. Its citation does not establish
that the current compiler ran that constructor or retains the corresponding
actual owner payload. This audit does not independently certify the cited
theory proofs or L1–L5.

## Exact production trace

1. `lower_module` calls `lower_module_with_counters`
   (`crates/yu-hir/src/module.rs:867`, `:901`). That function mints one HIR
   artifact token, assigns a root expression occurrence, and constructs a
   `DefinitionRootId` for an admitted binding (`:922–931`). These are
   artifact-branded structural registrations.
2. `lower_plan` constructs the sole `HirParameterId` from that definition
   root and ordinal zero (`:1293–1297`), pushes the parameter onto
   `ScopeStack`, lowers the body, then restores the stack (`:1310–1329`).
   `lower_leaf` checks the lexical parameter before the module namespace
   and copies its actual parameter handle into `NameResolution::Parameter`
   (`:1995–2006`). The Name therefore has a genuine construction-directed
   edge to this parameter. The stack contains lexical parameters, not a
   retained type-scope or dependent-telescope record.
3. `lower_plan` wraps that body in `ResolvedExpr::Lambda`, with the initial
   occurrence and the same parameter handle (`:1340–1346`), then forms
   `HirBinding` (`:1349–1358`). Its fields contain no source world,
   registration, invocation, publication or FinalRoot object (`:619–629`).
4. `ConstraintBatch::collect` enters `collect_mode` (`crates/yu-solver/src/lib.rs:855–859`).
   Collection creates a `DefinitionOrderId`, definition-value component,
   `CollectedDefinition`, and root lookup (`:932–1039`). For the Lambda it
   retains the parameter handle in `parameter_recipes` and calls
   `emit_lambda` (`:1153–1155`).
5. `emit_lambda` checks the body's `HirParameterId` against that recipe.
   For this Name it emits body effect constraints and stores
   `body_value_component: None` (`:1724–1740`). It emits Lambda effect
   constraints and retains a `LambdaRecipe` carrying occurrence, parameter
   position, root/body/effect positions and admission placement
   (`:1754–1775`; record type `:697–705`). This is a type-construction recipe,
   not a raw-provider or event owner.
6. Collection seals its term lineage and total lookup maps, then invokes
   `SccPlan::build` with collected definitions and definition uses
   (`:1236–1253`, `:1330–1335`). Its visible id path adds no external
   definition use for the parameter Name: the pending-use branch matches
   `NameResolution::Resolved`, not `Parameter` (`:1156–1180`). The SCC
   implementation itself was outside this audit lease.
7. `SolvedModule::solve` creates `InferenceSession` (`:16027–16028`).
   Startup allocates live parameter rows and level/metadata slots
   (`:9755–9767`). `admit_lambda_fact` chooses that same row as the negative
   argument and, because the body recipe has no value component, its positive
   result, constructs a Function term, and constrains the definition root
   (`:10790–10833`). This is real evidence of current F5 identity-function
   type construction; it is not evidence of the selected source laws.
8. `component_generalization_draft` selects a current live row through the
   definition root's component lookup (`:15490–15506`). SCC execution installs
   a finalized scheme in a slot (`:14156–14174`). `finish` ultimately moves
   HIR, schemes, closed types, projections, provenance, errors and store into
   `SolvedModule` (`:15970–15997`). Neither that move nor the scheme slot is
   the draft's semantic immutable binding-publication event.

## Supplier table

“New output” means an authentic source-owner output and its correspondence
argument are needed before freezing this record. It does not authorize code
or choose between draft representations or failure policies.

| Proposed record or premise | Current source/code supplier | Direct evidence locator | Exact gap | New source-owner output? |
| --- | --- | --- | --- | --- |
| Shape and empty-import structural admission | Ordinary header lowering, resolved HIR shape, opaque standalone import input | `module.rs:106–112`, `:2025–2076`, `:619–629`, `:901–904` | `SemanticImports` has only an empty public constructor and is ignored by this lowerer; there is no retained imports certificate. Header admission supports multiple visibilities. A new preflight must select the requested one-binding/error-free/unannotated exact shape and preserve its entrypoint assumptions. These facts do not certify an immutable semantic world. | New checked preflight output; existing syntax/identity inputs are usable. |
| Definition/root structural identity `r` | HIR artifact/root minting and binding owner | `module.rs:185–196`, `:922–931`, `:1349–1358` | The handle denotes this admitted definition, not a source-publication event or complete semantic root. | No replacement ID required; new semantic outputs must point to it. |
| Parameter identity `q` and Name identity/edge `(n,q)` | Parameter construction, lexical stack lookup, copied `HirParameterId` in resolved Name | `module.rs:271–302`, `:1002–1029`, `:1293–1297`, `:1995–2014` | Authentic lexical ownership exists. No type declaration, original type scope, telescope, provider or Name local-law certificate is stored. Generic aggregate equality also drops parameter owner information; see H-identity attack below. | Existing direct identity edge can be reused; semantic introduction/Name outputs are new. |
| Lambda identity `ell` and exact parent/body incidence | HIR wrapper contains the parameter and body; collection retains recipe positions | `module.rs:461–466`, `:1340–1346`; `lib.rs:697–705`, `:1153–1155`, `:1724–1775` | HIR tree and recipe positions identify occurrences. They do not establish authentic raw-provider formation or source Lambda/Result introduction. | New semantic Lambda/Result outputs. |
| Component identity `C_id` | Collected definition/root map and frozen plan construction | `lib.rs:510–515`, `:932–1039`, `:1156–1180`, `:1330–1335`, `:1481–1504` | Existing join can locate a collected SCC. Its full internal builder contract was not inspected. Even singleton/no-use topology is not a source `Internal(C_id,r)` relation, complete publication incidence, or initial-world validity. | New source component incidence/relation output; no claim that SCC identity must be replaced. |
| `d_a`, `sigma_a`, `Delta_a`, ordered `T_id` | Structural parameter plus ephemeral lexical stack; later F5 live row | `module.rs:378–394`, `:1002–1029`; `lib.rs:9755–9767` | None stores a Value-endpoint `Desc`, pre-challenge original type scope, dependency telescope or ordered source binder tree. Ordinal zero and level one describe different owner domains. | Yes: Parameter source introduction and scoped declaration/telescope outputs. |
| `Intrinsic_q`, flexible `I_a`/ValueInlet | Parameter identity and Function argument recipe | `lib.rs:697–705`, `:10790–10803` | No intrinsic source slot, entry/port/IF-path record or full flexible inlet schema exists in these fields. A negative parameter row is not that schema. | Yes: source intrinsic and ValueInlet outputs with original incidences. |
| Fixed `U_g`, `GenericValueInlet`, `IF0` | HIR Lambda shape; selected uniform Value-entry rule is cited as a mathematical supplier in draft §3.1 | `module.rs:461–466`; `lib.rs:697–705`, `:10798–10815`; draft §3.1 | Current code builds Function type terms. It does not retain actual raw-provider registration, Pure role, Value-entry code/port, independent generic inlet, fixed operands or original IF0 lifetime/scope. The theory citation was not independently audited here. | Yes: authentic source formation/inlet output and bridge to the HIR occurrence. |
| Complete `N_id`, including Name/Result/Call | HIR Name/Lambda structure and F5 effect/Function constraints | `module.rs:461–479`, `:1995–2014`; `lib.rs:1724–1775`, `:10790–10833` | No complete source relation, independent challenge/frame, Name restriction, decorated value/provider rebind, Result or original port projection is retained. Current constraints are not a semantic incidence manifest. | Yes: complete selected relation output. |
| Invocation/event/future binder schema | No supplier found in inspected ordinary record types; existing `AdmissionReceipt` belongs to constraint transactions | `module.rs:443–482`; `lib.rs:697–705`, `:3020–3030` | No receipt/Force, Return/Request/divergence, response/raw-resume prefix, formal rebind, event-proof scope or hereditary future schema exists here. Constraint-store admission receipt is a different receipt domain. Source schema operands can remain bound variables; no runtime event needs to be invented during construction. | Yes: finite source schema and explicit local-law dependencies. |
| `anchors_id`: inert registration | Value-shape classification; mathematical common `U_g` formation cited in draft §3.1 | `module.rs:438–440`, `:631–649`; `lib.rs:697–705`; draft §3.1 | `FetchValue` classifies syntax and is even retained as an unused future field. It supplies no registration, immutable world/allocation/lifetime tuple, role/port, capture certificate or dependent IF0 payload. | Yes: actual inert formation/anchor-owner output. |
| `anchors_id`: returned installation | No source execution/binding event supplier found; current admission/installation are solver events | `lib.rs:3020–3030`, `:10790–10833`, `:14156–14174` | No actual binding event, selected arm, `Executed`/`OneShot`, returned provider or same-world evidence tuple. Emitting a schema with binders cannot supply concrete fixed anchor operands. No inspected Rust branch chooses the allowed formation arm. | Yes if this arm is selected; needs actual owner output, not a fresh event tag. |
| Owner-certified empty captures | One parameter Name and no definition-use branch for that Name | `module.rs:1995–2014`; `lib.rs:1156–1180` | Structural no-external-Name evidence is available for this exact body. No raw-closure capture environment or source registration certificate is retained. Empty HIR captures and valid empty provider environment are separate claims. | New formation output/correspondence certificate; no scan of solver rows needed. |
| Complete source `R_id`/FinalRoot | HIR definition and Lambda root; current F5 root-component/live-row lookup | `module.rs:1340–1358`; `lib.rs:15490–15506` | The current lookup selects a solver generalization row. It does not construct the complete unannotated source synthesis root or its full source incidences before solving. An enum tag alone does not provide them. | Yes: selected FinalRoot output linked to the HIR Lambda. |
| Actual `p_id` and `(C_id,R_id)` immutable publication incidence | Structural `HirBinding`; later scheme-slot install and Rust result transfer | `module.rs:619–629`, `:1349–1358`; `lib.rs:14156–14174`, `:15970–15997` | No immutable source-binding publication object, event identity, selected root/component tuple or link to an actual anchor formation. Reusing a definition ID requires a restricted publication bijection proof, not just one field per HIR binding. | Yes: authentic publication-owner output and restricted correspondence proof. |
| `templates_id` / retain-fix output / `ScopedClosure` | No selected-source walk in inspected seam; current component generalization uses F5 | `lib.rs:15490–15506`; draft §§3.1, 4 | Selected records are absent, so there is no complete source-owned input graph from which the proposed walk could derive membership/fixedness. A static schema still requires a complete typed manifest and actual owner operands. | Yes: selected retain/fix construction over supplied source records. |
| Staging, frozen payload and terminal owner lifetime | Batch retains HIR/recipes/SCC; session owns batch; finish retains HIR and solve outputs | `lib.rs:796–827`, `:7419–7427`, `:7333–7362`, `:15970–15997` | No sidecar or publication/anchor-owner payload exists. Finish does not retain SCC plan or parameter/Lambda recipes as such. Keeping an Arc to a token keeps its identity alive, not the absent semantic payload or transitive owner graph. | New staging and terminal retention fields after approval; lifetime proof remains required. |

## H-identity attack

There is a positive, narrow construction fact: `lower_plan` creates one
parameter, makes it visible while lowering the body, restores the lexical
stack and wraps the result with that exact parameter. `lower_leaf` records
the selected parameter handle. This supports the structural part of the id
tuple without inverse reconstruction from F5.

Three limitations prevent upgrading that fact into an unconditional semantic
identity theorem:

- `NameResolution::PartialEq` compares only parameter ordinals
  (`module.rs:421–427`); `HirParameterId::PartialEq` compares the definition
  owner and ordinal (`:299–302`). `HirParameter::PartialEq` compares name/range
  (`:398–403`), and `HirBinding::PartialEq` compares structural fields without
  its branded definition root (`:679–688`). Therefore aggregate HIR equality
  is insufficient to establish same-owner Parameter/Name identity. The direct
  comparison in `emit_lambda` (`lib.rs:1729`) uses the stronger parameter ID
  equality and does preserve this join. This is an audit of a proof hazard,
  not a finding that ordinary lowering currently confuses two parameters.
- `owns_occurrence` and `owns_definition_root` check artifact-token equality
  (`module.rs:802–808`). They do not by themselves select a particular
  expression's role or parent incidence. Admission must check the actual
  binding tree and its handles. `owns_parameter` additionally checks binding
  and parameter membership (`:811–817`), but still supplies no semantic scope.
- Ordinary HIR retains ranges, tree shape and resolution. The source-node
  correspondence map is gated by `cfg(any(feature = "shadow", test))`
  (`module.rs:785–790`, `:934–940`, `:1298–1302`, `:1974–1979`). The ordinary
  path inspected here does not retain that exact source-node map. A bridge
  could prove the ordinary lowering case directly; it cannot claim a current
  production source-node certificate or silently make the shadow route its
  owner.

Thus structural H-identity is supportable at the actual construction sites,
with explicit owner-sensitive comparisons and constructor cases. The full
claim that these occurrences are the selected semantic introductions remains
conditional on a new constructor and its verified correspondence.

## H-bridge attack

The compact origin tuple records which parameter, Name, Lambda and component
the compiler chose. Its final-root and publication tags select intended rule
families. Neither tags nor private Rust constructors prove that an actual
source registration/publication with complete fixed operands occurred.

The decisive information test is the draft's own two permitted formation
arms. Its mathematical source discussion permits inert registration and an
actual returned installation of the same inert `U_g`. The current HIR tuple
and F5 Function recipe contain no arm discriminator, immutable world,
allocation/lifetime owner or `Executed`/`OneShot` identity. If admissible owner
evidence differs while those structural inputs agree, no function of those
inputs alone can recover which actual payload belongs to `p_id`. This is a
conditional information-loss argument, not a claim that the current compiler
executes both arms. Selecting one arm requires authentic supplied formation
evidence or an approved, proved restriction of the admitted constructor;
this audit makes no such choice.

The same test applies to original type scopes and IF0 lifetimes: lexical
nesting and a parameter ordinal do not encode arbitrary dependent source
operands. A compiled schema can describe binder positions and clauses, but
cannot replace actual fixed owner operands with fresh schema variables.
Conversely, event receipt/response/result operands that the selected rules
bind in a finite schema do not need runtime evaluation. The distinction is
between authentic fixed formation data and symbolic challenge/event binders.

An `Arc<IdPublicationOwnerRecord>` would solve a retention-reference problem
only after that record has an authentic producer, actual formation payload,
the `(C_id,R_id)` selection and proved transitive lifetime. The current
`DefinitionRootId` contains an artifact token and `DefId` payload
(`module.rs:185–196`); it is not such an owner. Scheme installation and
terminal success likewise do not fill these missing facts.

H-source and H-bridge therefore remain distinct. A complete selected-source
constructor must provide a manifest connecting each emitted semantic record,
binder, port and fixed operand to its actual construction rule and local-law
premise. H-bridge must then establish that the Rust output is that manifest,
including the selected formation and publication. The inspected code provides
neither output today. The source package remains ineligible for freezing on
these code inputs alone; this statement changes no source semantics and
supplies no F5 cutover authority.

## Bounds, omissions and task-record delta

Read scope was `rules/design-authority.md`, the hash-pinned draft, and the
relevant record/constructor/lookup/finalization ranges of
`crates/yu-hir/src/module.rs` and `crates/yu-solver/src/lib.rs`. Locators are
line references in that inspected workspace. The branch/HEAD above are the
assignment packet's baseline; no Git commands independently verified them.

Uninspected: parser implementation, `scc.rs` internals, imported theorem/source
documents and their proofs, VM/native/runtime registration or execution
owners, shadow modules, solver backends outside these ranges, full feature
combinations and unrelated production record families. Absence findings apply
to the exact ordinary HIR/solver construction seam inspected here, not to all
repository code. Runtime owner suppliers, if proposed elsewhere, require a
new bounded correspondence trace. No tests, builds, performance experiments
or Git operations were performed. Measurement consumed: zero samples and zero
measurement processes.

Task-record delta for primary integration: add this evidence locator to the
active id-only producer packet; retain H-bridge, original scope/telescope,
generic inlet/IF0, actual formation/publication/root and lifetime gates as
open. Record the owner-sensitive H-identity comparison hazard. No production
gate, proof obligation, representation or failure policy is closed by this
audit. Only this leased progress artifact was created; task/design/index/Git
synchronization remains with the primary.

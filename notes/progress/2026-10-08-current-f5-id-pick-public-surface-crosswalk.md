# Current F5 id/pick public surface: source-to-artifact crosswalk

Date: 2026-10-08
Baseline: `6982402afa95f93552bdd5954d22c852b27b3f92`
Branch: `research/simple-sub-intrusion`
Status: frozen research-only producer artifact; independent review pending
Claim class: conditional source-to-artifact mapping and bounded static derivation
Production implementation / semantic gate closure / cutover: none
Exclusive lease: this file only

## Objective, governing premises and method

Trace authentic `my id x=x` and the bounded literal-import source
`my z=0; my pick y=z` through current production HIR/F5, then compare its
actual outputs with the already selected transformed export. Authority is
[native export selection](../design/2026-10-08-native-projection-public-export-definition.md)
§§1–4 and [integrated construction](../theory/2026-10-08-projection-public-export-construction.md)
§§2–4, 6–8. The selection's recorded user decisions fix native formation,
complete ordinary production including non-source alternatives, actual public
root checking, and finite public imports. This note does not select another
language meaning or derive successor evidence from current solver success.

The method is inspection of pinned source constructors, record definitions,
and their exact call path. All production reads used `git show 6982402:path`.
The authority files initially read in the worktree were byte-equal to that
baseline when checked. HEAD initially observed was
`bd36a19e3839439af1dc65075bf3699c896a08a7`; relevant dependencies were unchanged.
The pending Flat-Application question and regression inventory conclusions
were not consumed.

Explicit hypotheses for the scalar-output derivation: the displayed source
lowers through the ordinary entrypoint without HIR errors; collection and
solving complete without availability failure; definitions are distinct and
the shown references have their unique resolved targets; there are no extra
constraints, annotations, conversions, or recursive definitions. Symbols
below name rows within one current solve session, never successor Desc/Slots.
This is a bounded characterization of these constructor paths, not an
independent proof that F5 transitions implement the native semantic laws.

## Pinned production derivation

Locators below refer to baseline line numbers and named functions, not a
moving branch position.

### 1. Parameter, Name and Lambda formation

`yu-hir/src/module.rs` defines `HirParameter` as id/name/range (378),
`NameResolution` as Resolved/Parameter/Ambiguous/Unresolved (414), and Lambda
as occurrence/parameter/body/range (461). Binding lowering (1290–1350) forms
one parameter at ordinal zero under the definition root, pushes it while
lowering the body, then wraps the body in Lambda. Identifier lowering
(1995–2019) prefers the parameter scope to the module namespace.

Thus id has `Lambda(q, Name(Parameter(q)))`; pick has
`Lambda(q, Name(Resolved(z)))`. The literal z retains spelling `0` in HIR.
These are genuine source resolution distinctions, but none of these records
contains native Desc scope sigma, `I_q[a;Delta]`, raw closure anchor,
`GenericValueInlet`, IF, world/permission/incidence records, or native local
checking proof terms. HIR identities protect artifact ownership, not those
semantic facts.

### 2. Collection and live Function admission

`ConstraintBatch::collect_mode` (`yu-solver/src/lib.rs`, 1090–1176) takes
Lambda through `emit_lambda` (1715). `LambdaRecipe` (697) stores occurrence,
parameter recipe position, root component position, optional body value
component, body/lambda effect component positions, and scheduling offset.

For id, `emit_lambda` checks the exact Parameter identity and gives the body
only its Effect component: `BottomEffect <= e_body <= EmptyEffect`. Its
`body_value_component=None` deliberately selects the parameter again at solve.
The Lambda likewise receives `BottomEffect <= e_lambda <= EmptyEffect`.
These four effects are collected facts; the fifth Function fact is admitted
from the recipe.

Startup (`try_new`, 9709–9768) allocates collected Value/Effect rows and one
additional parameter Value row, each initially at level one with
`non_generic=false`. `admit_all_collected_facts` (10685) inserts recipes at
their frozen offsets. `admit_lambda_fact` (10790) derives the parameter row p
from its recipe position and creates:

```text
id:   Function(argument=p-, argument_effect=Empty,
               result_effect=e_body+, result=p+) <= root_id
pick: Function(argument=p-, argument_effect=Empty,
               result_effect=e_body+, result=b_z+) <= root_pick
```

For pick, `emit_resolved_binding_name` (1673) allocates b_z and its empty
effect bounds, while collection records one DefinitionUse targeting z, with
`use_level=1`. The Name's slot-zero value relation is deferred to SCC routing.
For literal z, `emit_integer` gives its occurrence value v the bounds
`Int <= v <= Int`, its effect empty bounds, and `v <= root_z`. Its spelling
is not an operand of any emitted type constraint.

The positive Function term has four typed scalar/effect children. Its
provenance identifies the actual occurrence/cause, including Lambda local
slot 2; provenance is not an independently interpreted source-introduction
certificate. Nothing at this admission constructs a raw callable, inlet
image, force/body/return phase record, Echo, or Fixed(J_z) operand.

### 3. SCC closure and root schemes

`run` (9969) admits all collected facts, executes the frozen SCC plan, and
finishes. `execute_scc_plan` routes internal uses before member drafts
(13230), reads each member's exact root row through
`component_generalization_draft` (15475), normalizes the component drafts,
finalizes them, installs every member scheme (14154–14178), then routes that
component's incoming uses (14200–14250). The acyclic pick dependency therefore
installs z first and routes its Int scheme into b_z before drafting pick.

The actual current generalizer uses row levels/non-generic closure and
positive/negative incidence. `f5c_generalization.rs::post_r_selection_work`
(about 11015) gives a Q binder only to an eligible retained row occurring in
both polarities; recursive selection remains separate. The boxed producer
used by ordinary production (lib.rs 14140) eliminates eligible one-polarity
rows (`f5c_generalization.rs`, 11605–11890), with negative elimination to Top
in `f5c_binder_substitution.rs` (445). This is current F5 selection, not the
native Generalize fixed-dependency result.

Consequently the bounded scalar derivation is:

| Source root | Current closed scalar scheme |
| --- | --- |
| id | one Q binder, `Function(Q0-, Empty, BottomEffect, Q0+)`, no recursive bound; displayed `forall a. a -> a` |
| z | zero Q binders, Int |
| pick capturing that z | zero Q binders, `Function(Top, Empty, BottomEffect, Int)`; displayed `Any -> Int` |

For id, p survives in both argument/result polarity. For pick, the ignored p
occurs only negatively, is eliminated to Top, and b_z expands to Int. The
selected native pick retains its independent inlet template and displays
`forall a. a -> J_z.value_type`; current Top elimination cannot stand in for
that whole protocol or its certificate fields. This note makes no claim that
the two complete semantic interfaces are equivalent because their scalar
input displays look broadly usable.

Finalization (`finalize_generalization_draft_raw`, 15522–15660) translates
Function argument/result into closed handles and supplies Empty/BottomEffect.
`yu-types::ClosedValueScheme` (630) contains arena brand, quantifier count,
recursive-bound span and positive predicate handle. Its closed views (585–628)
contain Bottom/Top/Int/Q/R, Function children, Union/Intersection, and the two
pure effect leaves. They have no export payload or native certificate schema.

### 4. Incoming fresh uses and final result

For an additional ordinary alias `my use=id`, collection records a
DefinitionUse, and `route_incoming_inner` (15162) reads the finalized id
scheme. `instantiate_and_route_closed_inner` (14795) allocates one fresh
Value row at `use_level`, stores one substitution entry per Q/R binder,
restores any recursive bounds, decodes the closed predicate, and routes it
to the alias occurrence Value row. Both Q0 appearances reuse that same fresh
row; a different DefinitionUse gets another substitution. A corresponding
alias of literal pick has no Q/R image to allocate: it decodes Top -> Int.
This does not allocate the selected ordinary public root u_i or apply a
whole frame action to I/IF/Delta/typed proof telescopes.

`finish` (15740) publishes the retained schemes/ClosedTypeArena, projections,
HIR, ConstraintStore and routing provenance together in `SolvedModule`
(7333, 15972). Lambda projections are `Unknown` value with `Empty` effect;
z's ordinary literal projection is Int with Empty effect. `root_value_for`
(16100) reduces a Function root to Unknown. Closed Function structure can be
borrowed through the default-off `shadow_closed_schemes` observation surface
(`shadow_f5.rs`, 189–252). The ordinary production API does not publish a
ProjectionExport object or a native Direct certificate consumer.

Retaining HIR/store for current artifact queries is real current behavior.
It does not meet the selected export's prohibition on source graph access by
its exported object, nor prove a violation by an object that does not exist.

## Crosswalk and missing owners

| Selected field/lifecycle (§§3–4, 6–8) | Actual current output | Missing producer or consumer responsibility |
| --- | --- | --- |
| Same sole Desc a at original sigma and complete constraints | Parameter identity plus session row; id's Q sharing; pick's parameter eliminated | Parameter formation must retain typed declaration/scope/incidence and eligibility evidence before row projection. |
| Fixed immutable closure/provider anchor and GenericValueInlet(q,IF0) | HIR Lambda and Function term | Lambda/source formation must establish the actual fixed anchor and independently justified inlet. Shape/acceptance is insufficient. |
| Whole `I_q[a;Delta]`, IF, Force/future guards and whole-image proof | Scalar argument/effect children | Parameter/inlet construction must own full typed interface records and original input-image choices. |
| `EntryValue` / `PublicValue(J_z)` active result dependency | id reuses p; pick uses a Name Value row | Owning Bind/Read/Return/invocation rules must retain typed witness records and raw alias equations. Repeated scalar types do not prove Echo or fixed provider identity. |
| Actual finite installed import and full free dependency closure | DefinitionUse target/cause; z's Int scheme | Immutable capture installation must retain J_z once and monomorphically, including value/provider and its complete free fields. Current cross-SCC scheme freshening cannot certify a native fixed capture. |
| Worlds, ports, event and logical proof slots; Shared/ViewLogic/EventField/EventProof telescopes | Artifact/cause IDs and solver provenance | Source evidence owners must retain typed records and original choices; cause tracking has no such interpretation. |
| Extraction from actual final Generalize root; only forced raw aliases erased | Root row draft/normalization -> ClosedValueScheme | Publication must consume native Generalize/evidence and produce the finite export grammar. F5 incidence/census is not that extraction. |
| New ordinary u_i, one whole action; aliases reuse the same frame | Q/R-to-fresh-row substitution and scalar Term route | Public decode/use allocator must produce active ordinary equations and preserve fixed/shared/frame/event fields. A solver row is not a decoded complete ordinary root. |
| Independent complete VP production with non-source alternatives | Scalar Function constraints and empty effects | Ordinary interface interpretation must implement the selected phase grammar; actual source facts cannot manufacture or delete its extras. |
| Direct Value/Computation/complete Function certificate cases | Directed typed-pair solving; no public L term input/output | Ordinary checking must validate finite independently grounded local terms at actual u,V, including Any/union Value cases and complete Function domain/observation proofs. |

`f5c_tree_analysis`, `f5c_replay`, `f5c_materialization`, normalization and
binder substitution transform current scalar trees/Term DAGs and Q/R
references. Their walkers/materializers do not introduce missing interface
records. `f5c_draft::FlatDraft` is a private candidate scalar representation;
the ordinary production path remains boxed. These representations cannot be
treated as new native constructors by renaming their rows or node IDs.

## Smallest distinguishing witness and independence

Consider the two bounded sources, compared only at their closed pick schemes:

```text
my z=0; my pick y=z
my z=1; my pick y=z
```

They differ by one literal digit. `emit_integer` has no spelling/value operand
in its type facts, and the same topology produces the same Int import route
and closed `Function(Top,Empty,BottomEffect,Int)` schema up to arena branding.
The selected literal contracts have different actual values (0 versus 1), so
their active `PublicValue(J_z)`/Fixed(J_z) operands differ. No decoder using
only that closed scheme can determine which selected fixed-result operand to
install. Reading retained HIR to recover the digit would change the proposed
scheme-only input and still would not supply the independently grounded
ground certificate/provider/world fields.

This is a static information-loss witness, not an executed compiler
counterexample or a runtime unsoundness claim. It rules out recovering the
complete selected pick export **from the current closed scheme alone**.
It does not rule out lawful construction at the source-owned publication
boundary by retaining the missing canonical evidence. There is no claim of
global program-size minimality; the pair is minimal in changed literal payload
and uses one literal producer, one ignored formal and one captured Name.

The reference is the selected native export grammar; the candidate is the
pinned current producer/consumer record vocabulary. They are independent
descriptions, but this source inspection is not an independent validation of
the selected theorem's primitive laws or of F5 transition soundness. Shared
assumptions are the displayed source syntax, resolved-name ownership, and
ordinary Int literal classification. No supplied transition-rule checker,
independent execution oracle, randomized seed, search range, or mutation
campaign was used. The literal-payload change above is the one explicit
discriminating source mutation. Failure conditions include changed direct
dependencies, different lowering/resolution, additional constraints, and
solver availability failure. A future scheme carrying a grounded fixed
import/certificate payload would invalidate this scheme-only witness premise.

## Checks, coverage and residuals

Commands were bounded `git show`/`sed`/`rg` reads of the named constructors,
plus SHA-256 and baseline/worktree equality checks; no tests, builds,
benchmarks, formatting, Git mutation, or production edits occurred.
Existing baseline tests `f5d_identity_lambda_admits_exact_effect_and_function_facts`
and `f5d_constant_and_module_name_bodies_close_to_pure_functions` were read
only as corroborating code contracts, not executed or used as native authority.
The source derivation above explains their id Q=1 and constant/pick Q=0
assertions without treating those assertions as independent oracle results.

Coverage is one import-free immutable id, one literal-backed pick, ordinary
cross-SCC Name use, and a further ordinary alias use of either. It excludes
applications, conversions, annotations, unions/records as source bodies,
recursive SCC behavior, arbitrary hidden captures, State/foreign kernels,
runtime backend realization, full local proof search and production cutover.
Finite acyclic public projection/record imports are selected semantics but
were not traced through current production here. No broad search was attempted.

Resource budget consumed: read-only shell/hash work and one note write;
zero Cargo/heavy processes, zero experiment samples. At most three independent
lightweight read commands were requested together. CPU seconds, peak RAM and
total wall duration were not measured; no numeric performance claim follows.

Recommended next action: the primary should assign the source-formation/
publication architect an exact retained-record design packet for Parameter,
Lambda, fixed import installation and final-root extraction, using these
missing fields as its input inventory. That owner should specify the native
certificate producer and decode/check consumer interfaces before any
separately authorized production change. Another scalar Q/R probe cannot
recover evidence absent from its input.

## Frozen direct dependencies

SHA-256 at the pinned baseline; each was byte-equal to the worktree at the
dependency check. The full-file hash is the read-snapshot identifier; it does
not imply every section was inspected. Historical theorem review hashes in
its prose are distinct from this current whole-file hash.

| Path | SHA-256 |
| --- | --- |
| `notes/design/2026-10-08-native-projection-public-export-definition.md` | `aed6ef63b01f555a5f2804f87a599167c1a30fa999afc0b9d9f11b8ae974a919` |
| `notes/theory/2026-10-08-projection-public-export-construction.md` | `4cf84e7a38153b893f1d339780598e2b79084c747ecb883acf0e4fdaa49cf631` |
| `crates/yu-hir/src/module.rs` | `3bb488f9d9e13b43e79e472a65a35197ae4f2c76ae21a6f0f8f77195661f4363` |
| `crates/yu-solver/src/lib.rs` | `236f4f433ef775df0d88294f046e11dd34c1816da2fa99d7f0d403b39c2ed4a2` |
| `crates/yu-solver/src/term.rs` | `12ddbeb759e82c753c1674fb204c7344bd781f5f570ef226ac3fdcd57c1a9611` |
| `crates/yu-solver/src/f5c_generalization.rs` | `6f029758c19c99e397b9653af842b39ca680ece077b65322606266987515ab88` |
| `crates/yu-solver/src/f5c_binder_substitution.rs` | `6b2d9d53546fc2218132dad65fac8619ec125c65817af5fe42239ebc85ffee80` |
| `crates/yu-solver/src/f5c_normalization.rs` | `9beee5e5c230fdacaeacaa4ce5491b63343eb1ed75b95a266671694740ba80d9` |
| `crates/yu-solver/src/f5c_draft.rs` | `f6a670e2ded065e7751748e84f72dd1d86052242c7bc11a45b7f8d828af1b158` |
| `crates/yu-solver/src/f5c_materialization.rs` | `70ebbf9b0384111d1b3aab77b8718fa3c55cdc63143b3880896951872876f8e1` |
| `crates/yu-solver/src/f5c_tree_analysis.rs` | `f69fb7938dd22ba6cc65b8a1474e9e3f05c30af106c3ca110778b4a225807173` |
| `crates/yu-solver/src/f5c_replay.rs` | `7f23270342b43ab8e9f558e3d7b4db77f0f6cad9755f5b6cc7044337d499d92b` |
| `crates/yu-solver/src/shadow_f5.rs` | `b6a6c70da75329ff66cd9e6c0a2598a54cc8f0de7ba956f6f28b24616ca3a994` |
| `crates/yu-solver/src/scc.rs` | `3cfce9acfddd77838398cd95cd13c053f71f27a8367b07175a83c825d68a8df8` |
| `crates/yu-types/src/lib.rs` | `a3a920847b53e745ef17d43cf920c98a425e0d20c46b68524bd9c1d0b1a3fba5` |

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-08-current-f5-id-pick-public-surface-crosswalk.md`.
- Baseline SHA: `6982402afa95f93552bdd5954d22c852b27b3f92`.
- Changed dependency hashes: none observed; freeze/revalidation details above.
- Review status: producer artifact, unreviewed, research-only; no independent review claimed.
- Checks already run: pinned constructor/record call-path inspection and direct-dependency SHA-256/equality check. Existing tests were read only. No executable experiment or compiler verification run.
- Proposed one-line checkpoint message: `research: map current F5 id and pick to selected public export`.
- Shared-record deltas left for primary/curator: add the source-to-artifact result and scheme-only information-loss premise to the active implementation bridge; record exact source-record/decode/check owners as unresolved. No task/index/authority/theory-map/question-board file was changed; no aggregate gate should be promoted from this artifact.

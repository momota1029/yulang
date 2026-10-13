# Candidate Apply source-input owner map

Date: 2026-10-13
Branch supplied by primary: `research/simple-sub-intrusion`
Pinned baseline: `ce715b79abddc09073eda4571edb56afd8a99ddc`
Status: frozen, independently reviewed, non-authoritative bounded source characterization
Method: static constructor/registration/dispatch/consumer trace
Exclusive lease: this new note only; target absence checked before writing
Budget: one researcher, no descendants, at most 30 minutes; lightweight reads;
no builds, tests, probes, measurements or Git operations

## Objective, authority and claim class

Trace the actual owner of `ApplySourceInput`, compare it with a fallback
Apply recipe carrying `source_input=None`, and identify the first
missing construction and authority dependencies. No selected language meaning,
compiler path or proof status is changed.

Governing authority is [legacy withdrawal](../design/2026-10-10-simple-sub-legacy-withdrawal.md),
**Selected policy**, **Mechanism-by-mechanism completion evidence**, and **First
bounded retirement**; and [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md),
**§§1–5**, **Evaluation**, and **Authority and integration**. They require actual
replacement of obsolete dependencies while preserving source formation,
complete Call, effects, soundness, principality and normal inference. They do
not authorize discarding live Apply constraints or requiring a historical
Gen-Call-0 representation for every source Call.

The primary selected the exact next source boundary in `tasks/current.md`,
**2026-10-13 candidate fallback ownership audit**. Its reviewed dependency is
[candidate fallback audit](2026-10-13-candidate-fallback-withdrawal-owner-audit.md)
at commit `4f14d90a0`. This note refines that Apply boundary; it does not repeat
its whole fallback inventory. Workflow follows research-lab dependency/evidence
and frozen-lease rules, design-authority order, git-concurrency disjoint-file
rules, and the source-bridge guidance of `yulang-proofs`.

**Bounded result:** the fallback retains the native operands and actively
generates the same four-port Function demand and effect propagation as the
LocalSource Apply branch. It does not retain an authentic LocalSource Apply
index/children or the corresponding formal registration/use route. Existing
HIR constructors supply those records only within their own source arena;
there is no inspected conversion of a fallback retained expression into that
arena. Even an authentic `ApplySourceInput` supplies native incidence, not the
complete source Call judgment. Its pending-construction API explicitly lists
additional missing suppliers.

This is a static source characterization, not source acceptance, runtime parity,
an impossibility result, a conditional complete-Call theorem, withdrawal
completion, or independent review. In this note, **LocalSource Apply** names
`LocalSourceForm::Apply`; no separate `LocalSourceApply` Rust type was found in
the inspected HIR/solver cone.

## Construction and admission owners

Paths in source tables are repository-relative and refer to the dependency
bytes recorded below. Line spans are inspection locators, not proof substitutes.

| Boundary | Actual owner and retained evidence | Boundary that remains |
| --- | --- | --- |
| Lowering entry selection | `crates/yu-hir/src/module.rs:876–921`: ordinary lowering uses default counters; shadow Apply lowering installs source identity and `shadow_applications`; LocalSource lowering installs source identity and `local_source`. | Source identity alone does not set `local_source` or form its arena. These are distinct lowering products. |
| Per-Binding carrier | `module.rs:945,994,1008,1347–1428`: `lower_module_with_counters` forms the namespace and root, then passes them into `lower_plan`; `lower_plan` forms parameters, invokes `local_source::form` when selected, and inserts the carrier under the existing root before ordinary body lowering. `shadow.rs:46–59` rejects foreign-root lookup. | Collection receives an existing immutable carrier; it cannot infer one from a missing map entry. Rootless expressions have no such carrier. |
| Arena and occurrence formation | `module/local_source.rs:6–44,99–171,257–390,438–475`: indices contain the definition owner; `expression(index)` checks that owner. `Builder::slot` allocates the arena index; `Builder::set` obtains the exact source key, mints a distinct HIR occurrence, records source identity, range and lexical scope. | Native component ordinals and syntax positions are not `LocalSourceIndex` or the arena-owned expression. |
| Apply syntax | `local_source.rs:487–592`: reverse traversal of OperatorChain tails forms nested Applies for `MlArgument`, `CallTail`, and `ColonApplicationTail`, retaining exact callee/argument slots and `source_form`. Empty CallTail forms a separate Unit argument occurrence. Unsupported separators/tails and recovery/depth failures do not manufacture a Call. | This is nonshipping source formation, not a complete source-typing or invocation certificate. |
| Lexical construction | `local_source.rs:257–367,636–665`: actual parameters are installed before body formation; Names resolve from the current lexical environment, then the module namespace. Definition/Parameter/LocalInitializer/Expression scopes and local publication remain owned by HIR. | A formal recipe row cannot replace the source parameter object, its lexical Name, or its scope. |
| Facade preflight | `crates/yu-solver/src/shadow_apply.rs:78–115`: an owned LocalSource Binding uses `candidate_source::preflight` and placeholder handling. Otherwise retained Binding expressions use `preflight_expression`; rootless facade items must be Integer. | Passing this preflight is not source typing/admission. Internal callers bypassing it are a different input domain. |
| Source preflight | `candidate_source.rs:85–129`: validates supported annotation shapes, formal polarity/effects, operation declarations and resolved Names. | Negative concrete formal rows are rejected here; no migration may turn a missing supplier into an invented acceptance/rejection rule. |
| Fallback expression preflight | `shadow_apply.rs:787–857`: retained Integer/module Name/Group/Apply/Lambda forms, exact active parameter IDs, placeholder ownership and depth are checked. | This checks retained structure. It neither supplies LocalSource indices nor completes the Call obligations. |
| Collection choice | `crates/yu-solver/src/lib.rs:1124–1174`: with candidate graph effects, owned `hir.local_source(root)` selects `emit_candidate_source`; otherwise `emit_candidate_value` produces fallback facts/recipes and the schedule adapter. | The adapter retains indices into real constraints; it does not synthesize source evidence. |

The carrier and retained expression tree have separately minted occurrences.
Even where their syntax positions coincide, that is not branded occurrence or
arena-index equality; a migration needs an authentic owning construction.

The ordinary-carrier [proposal](../design/2026-10-10-ordinary-hir-successor-carrier.md)
is reviewed but not Authoritative. Its q1/a1 local approval bundle failed exact
content validation and remains unconsumed, as recorded in
[`receipt.md`](../../questions/2026-10-10-ordinary-hir-successor-carrier/receipt.md).
The proposal's **§1** identifies why directly selecting the opt-in switch
changes ordinary admission, diagnostics/refusals and occurrence order;
**§§2–3** propose an ordinary-owned sidecar contract; **§§4–5** retain
verification and approval boundaries. It is evidence of a known architectural
seam, not permission to implement that seam or proof that its proposed
representation is necessary.

## Apply field provenance and the fallback gap

`candidate_source.rs:180–246` allocates source component positions, actual
formal recipes and registrations, parameter Name endpoints, ascription aliases
and `FormalNameInput`s. Its Visit/Finish traversal retains source levels and
finishes operands before their enclosing Apply. `:394–411` is the only inspected
production constructor of `ApplySourceInput`.

| ApplySourceInput fields (`candidate_call.rs:30–47`) | LocalSource supplier | Fallback availability / missing evidence |
| --- | --- | --- |
| `owner` | Actual `source.definition_root()`; including an Apply within a nested local initializer, this is the carrier's outer module-definition root. | Collection knows the enclosing Binding root/order. The fallback recipe does not retain `owner`; it must not be relabeled as the resolved callee root or nested local owner. |
| `expression`, `callee`, `argument` | Actual Apply arena ordinal and its two owner-branded `LocalSourceIndex` children. | `ResolvedExpr::Apply` retains boxed children, occurrence, range and `source_form` (`module.rs:452–461`); `CandidateRelation::Apply` retains endpoint recipes. Neither supplies an index into a missing LocalSource arena. **This is the first code construction gap.** |
| `level` | The source Visit/Finish level; source component/parameter level maps retain the lexical initialization boundaries (`candidate_source.rs:251–300`). | Fallback creates no such lexical level map. Candidate startup defaults exist, but no source-level equivalence is established here. |
| `recipe` | Exact newly allocated candidate recipe index. | Fallback also has a candidate recipe index; no absent native recipe is alleged. |
| `callee_value`, `argument_value` | `endpoints[child]`, preserving actual formal endpoint reuse and source alias handling. | Fallback retains these endpoints, including its active formal-row lookup. They are native inputs, not source-child identities. |
| `callee_effect`, `argument_effect`, `result`, `application_effect` | Child/result component positions. | All four positions are retained by fallback `CandidateRelation::Apply`. |
| `checking`, `cause` | `ConstraintOccurrenceId(expr.occurrence, 0)` and its matching `CauseId`, retained at collection. | Fallback retains the recipe occurrence; admission constructs these same scalar provenance forms. That does not form an independent lexical/checking/complete-output source tuple. |
| `formal_name` | Optional route from the actual callee to a `FormalNameInput`, referring to the actual source Lambda registration. | Fallback Lambda retains a `parameter_recipes` entry and lexical stack, and parameter Name reuses that endpoint (`shadow_apply.rs:1125–1168,1218–1235`); it registers no source formal or formal Name. Native endpoint reuse is insufficient. |
| `native` | Initially `None`; exactly the later admission owner fills a generated `NativeInterface`. | Fallback generates the native demand/ports but has no source-input record in which to retain them. This is absent observation storage, not an absent live demand. |

The optional formal route is deliberately branch-sensitive. Direct Parameter
Names receive a registration; `Group`, `Ascription` and `Block` propagate that
route from their actual inner/final expression (`candidate_source.rs:412–473`).
ModuleDef, Local, Operation, Apply-result and Lambda-result callees have no
formal Name merely because their native endpoint is callable. This does not
exclude those Applies: they still receive their ordinary ApplySourceInput,
with `formal_name=None`.

Module Name handling keeps a different registration owner. Both source
`candidate_source.rs:369–392` and fallback `shadow_apply.rs:1192–1217` create
`PendingDefinitionUse(parent order, resolved DefId, occurrence)`. Source adds
an `Action::Module`; fallback schedules retain Module routing through the
adapter. These records support SCC/open-root and incoming-use routing. They
are not `FormalRegistrationInput`, whole original declaration registration,
typed module-Name admission, or receiving/export correspondence. There is no
license to put a module Name in the formal-registration slot.

`FormalRegistrationInput` itself retains source owner, actual Lambda index,
parameter identity and recipe position (`candidate_call.rs:16–22`); source
row initialization validates the recipe/parameter match and retains one
positive native root (`candidate_source.rs:532–560`). Source formal annotation
actions use that same recipe and scoped annotation (`:269–287,660–663`);
`candidate_effect.rs:1034–1111` constructs paired Value/Effect interfaces and
links the actual formal in both directions. These are real native annotation
owners; none constructs a whole original semantic registration from an endpoint.

## Deferred consumers and live graph constraints

`retain_candidate_relation` initializes **every** recipe's `source_input=None`
(`shadow_apply.rs:1057–1087`). LocalSource Apply then appends the record and
sets the exact recipe back-reference to `Some(index)`; fallback Apply
(`:1260–1285`) leaves it None. Planning retains obligations; it does not admit
or solve them early.

The actual deferred constraint consumers are:

1. Source schedule `Action::Candidate(index)` calls `admit_candidate_fact`
   (`candidate_source.rs:660–670`), after earlier operand actions. When source
   mode is inactive, `lib.rs:11123–11155` admits candidate recipes at their
   `after_collected_fact` cursor, interleaved with Lambda recipes/facts.
   `lib.rs:10336–10351` selects this execution branch. The fallback schedule
   insertion alone does not activate source mode.
2. With `source_input=Some`, `shadow_apply.rs:1312–1332` validates the registered
   recipe/back-reference, occurrence, checking occurrence, endpoint identities
   and all retained operand/result positions. This validation is skipped for
   fallback None; the demand generation below still executes.
3. `:1335–1388` converts both routes' native operands, allocates a fresh
   invocation Effect at the application row's level, and forms
   `Function4-(argument+, argumentEffect+, invocationEffect-, result-)`.
   For Some, it additionally retains callee/argument/effect/result/demand/
   invocation/application native fields once, refusing an already-filled
   record. Native initialization precedes constraint admission; the interface
   is not a proof that the eventual constraints succeed.
4. `:1390–1447` admits `callee+ <= demand-` with slot-0 occurrence/cause and
   actively calls `constrain_live_value`. Slots 1 and 2 propagate respectively
   callee evaluation Effect and invocation Effect into application Effect.
   Both routes submit these constraints. Argument evaluation Effect is the
   demand's argument-effect port; this map does not invent an extra eager
   propagation into the application row.
5. If an actual positive Function reaches that demand, `lib.rs:12493–12555`
   derives from the same pair the argument Value, argument Effect, result
   Effect and result Value obligations and enqueues their propagation.
   This conditional native pair decomposition is not complete provider
   admission or full invocation semantics.

The separate deferred **semantic construction request** is
`CandidateInference::source_call` -> `candidate_call::observe`
(`shadow_apply.rs:190–192`; `candidate_call.rs:282–456`) ->
`CandidateSourceCall::pending_construction` (`:206–243`). Observation borrows
the owned HIR arena and exact children; checks occurrence/scope, native demand
ports/kinds/polarities/invocation row; and, when present, follows the actual
Group/Ascription/Block callee route to its Lambda/Parameter Name registration.
It requires a filled native interface. The source constructors preserve the
formal-root association; the observer's positive-root shape check is not a
separate proof of complete formal applicability.

No inspected production caller consumes `PendingCallConstruction` to produce
a completed source Call theorem/certificate. The API returns supplier/input
inventories; the graph consumer above is the real executable constraint owner.
Search scope was the solver Rust source, including all occurrences of these
API names, not an assertion about every document or future consumer.

## Existing source rules and the first semantic supplier gap

The selected source APIs are present. Their absence must not be asserted merely
because Rust contains a pending marker.

| Existing rule/authority | Genuine premise supplied by that rule | What current Apply records fail to supply |
| --- | --- | --- |
| [Original Call formation](../design/2026-10-07-original-call-formation-definition.md) **§§1–4,6** | For an actual emitted Gen-Call-0 record, OSig-Demand/OC-CallEff introduce the complete invocation root and typed source incidence at the whole dependent tuple. §1 explicitly preserves Calls without such a record. | `OriginalGenCall0Input` (`candidate_call.rs:93–128`) lists B, X, Xi, Delta, declaration, argument interface, registered root, complete demand, beta, callee/argument lexical uses, Call/checking occurrences, immediate/complete output positions and ElimOrigin. The native record does not instantiate that tuple. Its negative Function is not the complete demand by declaration. |
| [Original Call owner](../design/2026-10-07-original-call-owner-definition.md) **§§2–4** | Whole original registration, actual resolved route, typed O0 and independent directional seed construct a shared source slot and protected upper owner. Endpoint matching does not introduce these premises. | Native formal registration retains actual parameter/source identity and one Value root; no whole original interface, introduction route or seed/checking exposure is formed. Module use routing supplies no formal seed. |
| [Registry adoption](../design/2026-10-10-original-registry-constructor-adoption-proposal.md) **§1 choices 1–6; §§2–3** | Source-owned pre-Call constructor API exists for the stated resolved nonrecursive formal/Name/Int fragment; complete declaration applications and lawful whole ordered substitutions remain required. | The first actual formal introduction still needs the whole original input telescope/ports and an authentic application. Native identity, lookup success and scalar endpoints do not instantiate them. This is a missing source-owned application, not a proof that no language rule exists. |
| `notes/theory/2026-10-07-call-input-construction-proof.md` **§§3.2–3.4**, especially Code-Call | Actual entry/closure/Call origins, Reify of the whole argument, VIncl and WholeArgCompatible origins, same actual provider interface, and complete result/ordered suffix ports. | Native four-port demand/checking provenance lacks those complete carrier/check/result/future interfaces. The previously reviewed [invoke owner inventory](2026-10-11-invoke-source-owner-inventory.md), **Positive owner evidence**, records the same distinction between existing APIs and missing actual applications. |

`PendingCallSupplier` names these unprovided compiler suppliers explicitly:
original registration whole interface, actual formal introduction, original
checking/seed exposure (only on its formal route), and for every observed Call
original Gen-Call-0, argument Reify/whole carrier, receiver dispatch/complete
result/future interfaces. Its unconditional Gen-Call-0 marker is an inventory
for this particular presentation, not authority to reject an ordinary source
Call using another valid derivation. A different source proof must still
establish the complete semantic content.

There are therefore two distinct obstructions. **At the fallback Rust record
boundary**, no actual arena-owned Apply/children/registration bridge is
constructed. **At complete source Call formation**, even the existing genuine
LocalSource record leaves the complete original constructor applications and
semantic transport unestablished. This bounded map identifies no globally
absent language rule, contradictory source rule, or uniquely earliest semantic
binder across all possible complete declaration dependencies.

HIR's existing source-position locators (`shadow.rs:675–743`) can join an
occurrence/parameter to exact syntax in an owning artifact. They explicitly
supply no typed slot/role judgment. Skeleton Apply/direct-Use/captured-call
locators (`:2211–2290`) retain structural incidence and pending premises, use
their own identities/domain, and do not produce LocalSource indices or a
complete Call. No cross-cast or endpoint duplication is justified by them.

## Downstream scheme/generalization obligations

LocalSource Apply constraints precede the owning scheme operations. Module
uses select an open monomorphic live-root route within the active SCC, or
`route_incoming` for a published target (`candidate_source.rs:672–677`).
`candidate_scheme.rs:843–935` executes all active component schedules before
capturing any member graph, stages all captures before publication, and keeps
active internal uses separate. `:945–975` recaptures the live target for an
incoming use and freshens its retained graph; no source Call record is made
from that successful freshening.

Local initialization emits its one-shot Effect into the block before
publishing a Value boundary (`candidate_source.rs:309–329`). PublishLocal
installs the actual local root/boundary (`:624–629`;
`candidate_scheme.rs:1316–1335`); later local uses capture/freshen the live
graph at their use level (`:1347–1407`). Parameter aliases keep their one
formal row. None of these consumers makes complete source-Generalize true
merely because capture or reconstruction succeeds.

[Native source Generalize](../design/2026-10-08-source-generalize-definition.md)
**§§2–4** retains every local clause/residual, actual final source/annotation
root, real binding/provider, fixed dependencies and rigid scopes, separate
independent frames versus monomorphic aliases, one-shot initialization,
complete incoming relations and lawful future uses. Apply migration must
preserve those contracts together with annotations, effects/protection,
lexical/captured/module identity, source scope/levels and provenance. Public
projection/checking and full Call/source correspondence remain separate open
obligations. No blanket rollback requirement is added beyond top-level
necessary abnormal safety.

## Static derivation and bounded coverage

Explicit hypotheses: (H1) execution uses the pinned facade and true/true
candidate collection; (H2) the source/HIR constructor and preflight succeed;
(H3) collection/native initialization/admission complete without availability
failure; (H4) the inspected source bytes are those below. No satisfying source
typing or completed Call judgment is assumed.

Under H1–H4, take a rooted retained `Lambda(f, Apply(Name(Parameter f), Int 1))`
with no LocalSource carrier (the shape of `my invoke f = f 1` through the
shadow Apply constructor). Fallback Lambda appends `f`'s parameter recipe;
Name resolves that active recipe; Integer retains its own Value/Effect
constraints; Apply retains endpoints/effect positions with None; deferred
admission constructs the demand and submits all three Apply constraints.
`candidate_calls.calls` receives no ApplySourceInput from this branch, so
`source_call` has no record to observe for that Apply. The same owned
LocalSource shape instead registers the actual Lambda and Name, appends the
Apply record, and later fills its NativeInterface. The pending complete-Call
supplier inventory remains on that positive branch too.

This is a branch derivation discriminating live constraints from available
source observation. It is not an executed fixture, minimized semantic
counterexample or rejection proof. No oracle ran; static source and documentary
rules are different evidence inputs sharing the selected authority, not two
independent semantic implementations. Seeds/ranges/mutations: not applicable.
Omitted paths or a changed constructor/consumer dependency invalidate the
claimed map rather than silently extending its coverage.

Commands/checks: target absence; bounded `cat`, `sed`, `rg -n`/`rg --files`
reads; SHA-256 dependency snapshots. Initial combined captures truncated and
two guessed HIR source-module globs were absent; actual
`module/local_source.rs` and decisive clauses were then read narrowly.
No absence claim relies on truncated captures. Build/test/probe/benchmark/
measurement counts: **0/0/0/0/0**. Shell reader process counts, CPU time,
peak memory and elapsed wall time were not instrumented. One leaf, no child,
no Git operation; only this leased note was written.

Unverified: runtime source acceptance/parity, actual complete declaration
applications, grammar-wide coverage, additional internal/manual HIR
construction, complete typed ports and operator semantics, all propagation/
extrusion/intrusion invariants, generalized/public scheme correspondence,
resource behavior, soundness/principality/termination and F5 cutover.

**One recommended next action:** retain the live source/Apply constraints while
the primary assigns the exact missing authentic constructor/application bridge
under its existing gates. This note supplies no implementation design or new
semantic choice; the ordinary-carrier proposal's approval boundary stays open.

## Frozen dependency snapshot

Primary supplied the baseline; this worker performed no Git reads or mutations
and does not certify HEAD equality. SHA-256 values identify the inspected
bytes for primary comparison. The older audit's overlapping source/authority
hashes matched. Final dependency recheck found no changed hash.

| Dependency | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/module.rs` | `943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-hir/src/shadow.rs` | `687b49061273974fe874a8479a8db91ba24cc77fe92e6d2b96ae46a3626cf9dc` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `crates/yu-solver/src/shadow_apply.rs` | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_call.rs` | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `notes/design/2026-10-10-simple-sub-legacy-withdrawal.md` | `93c2bf1c425522fdb41d0f4120d8430597a6091014741a64546e9fedb7bcf79a` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-07-original-call-formation-definition.md` | `4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f` |
| `notes/design/2026-10-07-original-call-owner-definition.md` | `0b86e367cf8170f4f9d095f0afe8e9f6003209189dc358e294941727962ff110` |
| `notes/design/2026-10-10-ordinary-hir-successor-carrier.md` | `82d98a38208c2cab7788b97deec8f1319734dbaddd41de70a7e56bae00fea689` |
| `notes/design/2026-10-10-original-registry-constructor-adoption-proposal.md` | `2d6439507f01f38234909f98d86b1d2fbe31d3c7dd60d453cf1c199604020451` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-07-call-input-construction-proof.md` | `f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6` |
| `notes/progress/2026-10-13-candidate-fallback-withdrawal-owner-audit.md` | `d57651250ce30e32860dc5291d14593c8579223724c233a7657043536a316843` |
| `notes/progress/2026-10-11-invoke-source-owner-inventory.md` | `62584157449ee7507d0d88e362bab0af913493b10997ea282e7fcd9d639e6e3c` |

Other neighboring research notes were used only as locators to direct source
or governing sections; no theorem premise is imported from their producer
claims. Live task/startup/index records are navigation and packet context,
not replacements for the pinned source and Authority.

## Commit packet

- Exact leased path: `notes/progress/2026-10-13-candidate-apply-source-input-owner-map.md`.
- Baseline: `ce715b79abddc09073eda4571edb56afd8a99ddc`, primary pinned.
- Dependency hash changes: none observed across recorded snapshots; primary
  baseline equality check remains its integration responsibility.
- Claim/review status: frozen, independently reviewed bounded characterization;
  no theorem, source acceptance, withdrawal or production authority.
- Checks already run: target absence, exact constructor/field/dispatch/consumer
  reads and SHA-256 snapshots; no tests/builds/probes/measurements/Git operations.
- Proposed checkpoint message: `research: map candidate Apply source inputs and pending Call owners`.
- Shared-record deltas left to primary/curator: link this characterization from
  `tasks/current.md` if accepted; distinguish the missing authentic arena bridge
  from unprovided complete semantic applications; retain live Apply constraints
  and existing source/Call/generalization/public-cutover gates OPEN. No shared
  task/index/authority/theory/question file was changed.

### Primary review and minor repair

`spec_auditor` passed authority and scope conformance. `compiler_referee`
passed the bounded source/consumer claims and identified one minor locator
correction: `lower_module_with_counters` forms the namespace/root and passes
them to `lower_plan`; `lower_plan` forms parameters and the carrier. The row
above was corrected to cite `module.rs:945,994,1008,1347–1428`. Direct source
inspection confirmed those ownership points. No proof or production gate was
promoted; no tests or builds were run.

# Candidate fallback: constraint ownership and withdrawal boundary

Date: 2026-10-13
Branch supplied by primary: `research/simple-sub-intrusion`
Pinned baseline supplied by primary: `3e489f7ac9507023d0901bf882d68375529334c6`
Status: frozen, independently reviewed, non-authoritative source characterization
Method: bounded static producer/dispatch/consumer audit; no executable experiment
Lease: this new note only; target absence checked before writing
Budget: one researcher, no descendants, at most 30 minutes; lightweight reads only

## Authority and exact claim

The governing withdrawal policy is
[`2026-10-10-simple-sub-legacy-withdrawal.md`](../design/2026-10-10-simple-sub-legacy-withdrawal.md),
especially **Selected policy**, **Mechanism-by-mechanism completion evidence**,
**First bounded retirement**, and its four subsequent implementation deliveries.
The inference principles' **§1 Prefer the mathematical structure**, **§3 Derive
implementation from proof**, **§4 Require only necessary abnormal-path safety**,
and **Authority and integration** preserve normal generation and genuine Call,
effects, source correspondence, soundness, principality and cutover obligations.
The source audit follows `rules/research-lab.md`'s dependency, lease, evidence and
checkpoint rules; `rules/design-authority.md`'s authority order and active
withdrawal clause; and `rules/git-concurrency.md`'s disjoint-file protocol.
`rules/agent-orchestration.md`, current task/startup records, design-index
withdrawal locators and the `yulang-proofs` skill were read. This leaf supplies
source evidence to the primary; it neither delegates constructive proof nor
certifies this output independently.

**Bounded conclusion:** for `CandidateInference::solve` and the inspected HIR
constructors, the fallback is still a producer of live value/effect constraints.
`candidate_legacy_actions` adapts their retained indices into schedule actions.
Its name supplies no evidence of F5 invocation. The candidate graph consumers
select live graph capture/freshening before the legacy closed SCC and scheme
consumers. Deleting the fallback would discard real literal, binding, parameter,
Group, Apply and Lambda obligations unless those producers and their consumers
are migrated first. No such replacement/coverage is established by this packet.

This is a source characterization, not a theorem of source admission, semantic
equivalence, retirement completion, production conformance or F5 replacement.
The precise premise is that execution enters the actual facade at
`shadow_apply.rs:78–115`, collection has both candidate flags true, and successful
`try_new_candidate` installs the candidate graph before `run_candidate` executes.
Internal callers that bypass preflight are a separate input domain. No source
meaning is selected or narrowed here.

## Entrypoints and HIR ownership

All source locators below are relative to the repository and refer to the frozen
dependency bytes listed at the end.

| Boundary | Exact owner and fields | Branch result |
| --- | --- | --- |
| Public private-candidate facade | `crates/yu-solver/src/shadow_apply.rs:78–115` | A Binding with an owned `LocalSource` goes through source preflight. Otherwise a Binding may use retained `ResolvedExpr`; a rootless item must be Integer. Other items fail `Unsupported`, apart from effect-declaration placeholder handling. |
| Expression validation | `shadow_apply.rs:787–857` | Iterative depth budget 128; resolved module Names, integers, Groups, Applies and lexically active parameter Names are admitted as retained shapes; Lambda pushes/pops exact parameter IDs. Apply placeholder IDs are retained as permitted errors. Unresolved/ambiguous Names, Error and out-of-scope parameters fail. Validation receives no historical Call inventory sink. |
| Final HIR error check | `shadow_apply.rs:104–109` | Only selected `UnsupportedExpression` placeholders and owned declaration `UnsupportedItem` placeholders are permitted. Shape validation is not source typing/admission. |
| Collection owner | `crates/yu-solver/src/lib.rs:983–1117,1124–1174` | Binding registers its root/order/component and body fact range; rootless expression has neither parent nor root. With graph effects, owned `hir.local_source(root)` selects source generation; lookup failure is `NonTotalDefinitionMap`. Missing carrier or missing root selects `emit_candidate_value`. |
| Historical fixture branch | `lib.rs:1137–1154` | `shadow_local_binding` and `emit_candidate_local_value` require `!candidate_graph_effects`; therefore unreachable under the pinned true/true facade route. They remain live in the historical false-effects route. |
| Schedule retention | `lib.rs:1162–1172` | Fallback actions go into `Plan.schedules[root]` or `Plan.loose`. This insertion does **not** set `Plan.active`. |

`HirModule::local_source` validates exact root ownership and only queries its
retained map (`crates/yu-hir/src/shadow.rs:46–59`). Missing carrier is not proof
of invalid source. Ordinary `lower_module` and source-identity lowering do not
set `LoweringCounters.local_source`; shadow-application lowering sets only its
own flag (`crates/yu-hir/src/module.rs:876–921`). LocalSource lowering sets the
source flag, and `lower_plan` forms/inserts a carrier for each admitted Binding
before ordinary body lowering (`module.rs:1347–1428`). Rootless items instead go
to `lower_direct_root_expression` (`module.rs:1361–1375,1493–1562`).

The inspected public constructors therefore distinguish two meaningful cases:

1. A module lowered without LocalSource has rooted fallback producers, but no
   source emitter sets `Plan.active`; their generated schedules are dormant and
   their facts/recipes are consumed by the global admission branch below.
2. A module lowered with LocalSource gives each admitted Binding its own carrier.
   Rootless Integer items still use fallback; when at least one Binding emits
   source, their loose schedule is actually executed. This is a genuine consumer
   of the adapter even though its emitted Module actions are no-ops for literals.

A rooted missing-carrier schedule **with active source mode** is supported by
the solver dispatch. Its formation through an additional public HIR constructor
was not established: the inspected LocalSource lowering forms every admitted
Binding carrier. This is a bounded constructor observation, not a global
unreachability claim. The solver's own internal bypass callers and manually
altered test artifacts do not establish ordinary source reachability.

## Complete fallback producer branch inventory

`emit_candidate_value` is `shadow_apply.rs:1089–1122`. It sends an outer Lambda
directly to the definition root; other expressions produce an occurrence
endpoint and, for a Binding, fact slot 10 links that endpoint to its root.
It initializes the exact lexical formal-position stack. A rootless Lambda
would fail `MissingDefinitionEndpoint` here and is already rejected by the
facade. A rootless non-Lambda succeeds only for Integer under facade preflight.

| Retained expression branch | Producer fields and constraints | Consumer obligation retained |
| --- | --- | --- |
| Integer | `shadow_apply.rs:1187–1191` calls `lib.rs:1699–1754`: occurrence Value/Effect positions, Int-positive <= Value <= Int-negative, Effect-bottom <= Effect <= Empty-negative (slots 0–3). Fallback Binding adds root link slot 10. | Exact primitive type, pure literal computation, root association and occurrence/cause provenance. |
| Resolved module Name | `shadow_apply.rs:1192–1217`; `lib.rs:1758–1799`: occurrence Value/Effect, pure Name effects slots 1–2, plus `PendingDefinitionUse { parent_ordinal, target DefId, occurrence }`. Parent is mandatory. | Source resolution, receiving occurrence, real target root, dependency/use route and its live or generalized value. Value slot 0 comes from routing; it is not fabricated during generation. |
| Parameter Name | `shadow_apply.rs:1218–1235`: reverse lexical lookup by exact `HirParameterId`, `CandidateEndpoint::Parameter(recipe_position)`, new Effect component and pure lookup slots 0–1. No module use is produced. | Exact lexical parameter identity and pure lookup after entry rebinding; unresolved lookup fails. |
| Nested Lambda | `shadow_apply.rs:1237–1245,1123–1177`: new occurrence Value, parameter recipe ID/position, recursive body endpoint/effect, own pure construction Effect, then `LambdaRecipe`. Outer Lambda uses its registered definition root instead. | Formal ownership, body Value and computation effects, closure construction purity, Function generation and entry/invocation effects at the consuming Lambda. |
| Group | `shadow_apply.rs:1246–1260`: child Value endpoint and child Effect, result Value/Effect components, retained `CandidateRelation::Group`. | Value forwarding and child computation Effect <= result Effect. No fixed-empty result effect in true graph mode. |
| Apply | `shadow_apply.rs:1261–1281`: recursively retained callee/argument Value endpoints and Effects, result Value/Effect, `CandidateRelation::Apply`. | Callee Function demand, argument value and computation effect, result value, invocation effect and callee evaluation effect. Full Call semantics remain separate. |
| Remaining `ResolvedExpr`/Name cases | `shadow_apply.rs:1282`; facade preflight `:809–854` | Error/ambiguous/unresolved/out-of-scope forms fail, preserving the checks. No silent truncation or empty substitute is constructed. |

Shared recipe fields are `occurrence`, relation, `after_collected_fact` and
`source_input` (`shadow_apply.rs:859–883,1055–1087`). Both relations store both
Value and Effect positions; parameters may be endpoint variants rather than
ordinary occurrence Values. Fallback always sets `source_input: None`.
`candidate_component` sets pure effects only when graph effects are false
(`:1026–1054`); graph Apply/Group retain effect variables. Lambda construction
purity is explicitly generated by `candidate_local_lambda_effect` (`:982–991`).
`LambdaRecipe` retains occurrence, parameter position, root component, body Value
endpoint, body Effect component, Lambda construction Effect component and the
fact cursor (`:1158–1166`). These are actual constraint inputs, not legacy
closed scheme slots.

Collection resolves pending module uses only after all definition endpoints
exist (`lib.rs:1271–1337`). It retains exact use ID/cause, parent/target order IDs,
occurrence, receiving/target components and `use_level` (source-map value or
fallback 1). Startup assigns level 1 to fallback components and parameter rows
before applying any explicit source-level maps (`lib.rs:10047–10103`). The
fallback does not construct LocalSource's lexical level maps. No equality of
its generalization/source-scope behavior to a replacement is proved here.
Collection seals its maps and builds the real SCC plan (`lib.rs:1337–1348,
1408–1422`); duplicate/missing ownership failures remain checks to preserve.

## Adapter and actual consumer dispatch

`candidate_legacy_actions` (`candidate_source.rs:506–528`) walks the closed
cursor interval `start..=end`. At each cursor it emits all matching Candidate
recipes, then Lambda recipes. For each actual fact it emits one Module action
per distinct occurrence followed by Fact. The terminal cursor is needed for
recipes formed after the last collected fact. It retains recipe indices, fact
indices and occurrence identity; it does not solve a constraint or allocate a
closed scheme. Its HashSet and Vec reservations can fail collection; they are
real adapter storage, not evidence of an unused F5 startup reservation.

`Plan.active` starts false (`candidate_source.rs:7–15`) and is set only after
successful `emit_candidate_source` (`:497–500`). Two consumers are essential:

| Dispatch branch | Exact owner | Consumption |
| --- | --- | --- |
| Source active | `lib.rs:10337–10348`; `candidate_scheme.rs:879–884` | Loose actions run first; SCC member root schedules then run with active open roots/uses installed. |
| Source inactive | `lib.rs:11123–11155`; `candidate_scheme.rs:885–889,917–929` | Global facts/recipes are admitted using the same fact cursor order; open SCC uses route before capture, incoming uses after capture. Dormant fallback schedules are not needed to invoke the constraints on this branch. |

Action execution is `candidate_source.rs:660–678`; normal schedule framing,
cursor progression and completed/suspended behavior are `:562–658`.

| Action | Exact consumer and resulting operation | Legacy dependency assessment |
| --- | --- | --- |
| Fact(index) | `lib.rs:11157–11230`: store admission and provenance, then `constrain_live_value` or `constrain_live_effect`; CrossKind records an error, other admission failures return. | Normal retained constraint propagation. No closed draft/finalizer call at this owner. |
| Candidate(index), Group | `shadow_apply.rs:1308–1334,1390–1424`: child-positive <= result-negative; effect forwarding slot 1 through `admit_candidate_effect` (`:1450–1473`). | Live value/effect constraints. False-effects pure observer behavior is a separate consumer branch. |
| Candidate(index), Apply | `shadow_apply.rs:1335–1388,1390–1447`: allocate fresh invocation Effect at application row level; negative Function demand contains argument Value, argument Effect, invocation Effect and result Value; constrain callee-positive <= demand; slots 1–2 propagate callee evaluation and invocation Effects into application Effect. | Four-port live constraint construction and propagation. This is not a complete source Call theorem, and no fallback `NativeInterface` registration occurs when source_input is None. |
| Lambda(index) | `lib.rs:11233–11370`: parameter negative domain (or explicit graph formal domain), body positive Value/Effect; graph mode allocates entry/returned Effect rows and generates entry <= returned and bodyE <= returned, retains inferred-entry provenance, then constructs positive Function <= root. | Uses the implemented entry-effect replacement; does not require empty argument evaluation. Pure Lambda construction/lookup facts remain necessary. False graph mode has the historical empty argument-effect branch at `:11339–11340`. |
| Module(occurrence), no use record | `candidate_source.rs:672–677` | No-op; covers literal/parameter/Lambda/effect/root-link occurrences that have no matching DefinitionUse. |
| Module(occurrence), active SCC use | `candidate_scheme.rs:938–944`; `lib.rs:15760–15783` | Validate exact open use/root membership, then ordinary live target-root <= use-value route with original identity/cause. No closed instantiation. |
| Module(occurrence), incoming use | `lib.rs:16461–16525,16681–16689`; `candidate_scheme.rs:947–979,981–1019` | Shared validated route transaction delegates immediately to graph capture and per-use freshening when candidate_graph exists. Fresh local generic rows are allocated at use level; nongeneric/shared rows retained; stored constraints are restored. Legacy scheme access begins only after the graph early return. |

Graph SCC execution captures every member before publishing any member graph
(`candidate_scheme.rs:842–937`). `lib.rs:14622–14639` returns to that graph owner
before legacy `execute_scc_plan_inner`. Startup's `legacy_closed` is false in
true-effects mode (`lib.rs:9726–9730`), so finalization is None and legacy
scheme-slot/draft reservations are skipped (`:9841–9846,10035–10046`). Candidate
finish checks that closed data are absent and schemes empty (`:10360–10373`).
These exact discriminators establish the local closed-owner bypass; the names
of shared `F5b` reserve lanes or resource samplers do not establish F5 closed
execution. Shared routing transactions, propagation and accounting remain real
candidate dependencies and are not retired by this audit.

## First unresolved construction boundary and remaining legacy owners

The first missing replacement evidence is at **expression-to-source construction**.
Fallback Apply has no `ApplySourceInput`, and fallback Lambda/parameter Names
do not create the source formal/name registration tables. LocalSource Apply
does retain owner root, expression index, callee/argument LocalSource indices,
level, recipe index, six value/effect coordinates, checking occurrence/cause,
formal-name link and pending native interface (`candidate_source.rs:394–411`;
`candidate_call.rs:30–59`). Its consumer validates those coordinates and fills
the native interface (`shadow_apply.rs:1312–1328,1367–1385`). Both routes still
lack complete Call/source meaning as described by their public unresolved
premises (`shadow_apply.rs:7–50`; `candidate_call.rs:81–119`).

Thus migration needs a real owner preserving the fallback's accepted retained
HIR, exact parameter/module identities, checks, scopes/levels, Value/Effect
constraints, provenance and use-time generalization, while constructing the
required authentic Call/formal inputs. Deleting fallback, relabeling the
Function inequality as complete Call, or assuming LocalSource lowering has
identical coverage does not supply this bridge. No annotation permission-field
decision is needed to report this earlier structural gap, and this note adopts
neither option in the separate pending annotation question.

Exact still-live legacy closed consumers in the inspected cone:

- `ConstraintBatch::collect` → false candidate flags (`lib.rs:892–902`) → normal
  session/SCC closed owner (`:14633–14642`) and closed incoming scheme branch
  (`:16690–16765`).
- `CandidateValueObservation::solve` → `collect_mode(hir,true)` → graph-effects
  false → `SolvedModule::solve_with_shadow_fresh_capture`
  (`shadow_apply.rs:510–586`). Its genuine Call inventory, closed scheme and
  historical local fixture consumers retain actual ownership. The shared
  `emit_candidate_value`, recipe and Lambda helpers cannot simply be deleted
  while this public historical route still calls them.
- When `shadow-f5` is enabled, collection retains a pending-application sidecar
  before branch selection (`lib.rs:1121–1122,1443–1484`). It stores occurrence,
  enclosing root, operand occurrence/direct Name resolutions and an unresolved
  typing marker. The inspected production readers are observer inventory APIs
  (`lib.rs:1438–1439`; `shadow_f5.rs:99–103,135–185`) and frozen result transfer
  (`lib.rs:17553`). It does not drive the four candidate action consumers.
  This sidecar is separate from the retired discarded preflight
  `Vec<CandidateCall>`; this audit does not authorize its removal or establish
  that every observer caller can migrate.

No implementation dependency is removed by this note. The prior withdrawal,
closed-lifecycle, unused-draft, entry-effect and discarded-inventory deliveries
were read as bounded historical deliveries; their reported test counts were
not reused as present fallback coverage or proof. The genuine source/checking,
Call/effect, scope, safety, soundness, principality and public cutover gates stay
open under their current owners.

## Smallest static owner witness, verification and omissions

The minimal live producer witness is one retained
`HirItem::Expression(ResolvedExpr::Integer { occurrence, spelling, range })`.
Facade preflight accepts that item; collection has no root, so the fallback
produces four literal facts and loose actions. With no source Binding,
`Plan.active=false` and global admission consumes all four facts. With an
additional genuine LocalSource Binding, `Plan.active=true` and the loose
schedule consumes those same facts. This is a static branch derivation from
the cited constructors, not a run or an assertion that a raw text fixture
parsed/admitted/executed successfully. It discriminates the claim that the
fallback and its adapter have no genuine consumer without assuming any new
source semantics.

Commands used: `test ! -e <leased-note>`; bounded `cat`, `sed`, `nl -ba`,
`rg -n`/`rg --files` source/rule/record reads; `sha256sum` over the fifteen
direct code/authority/delivery dependencies. One erroneous exploratory locator
`crates/yu-hir/src/shadow/` returned absent; the actual `shadow.rs`, `module.rs`
and source module layout were then located. No conclusion depends on that
failed directory lookup. Large initial record captures were truncated; the
governing rules and relevant source/record sections were reread narrowly.

Build/test/probe/benchmark/measurement process counts: **0/0/0/0/0**. Seeds,
ranges, mutation checks and oracle independence: not applicable, because no
executable model or oracle comparison ran. Ordinary shell source-reader process
counts, CPU time and peak memory were not measured. Wall budget stayed below
30 minutes. No Git operation, compiler/config/test/manifest edit, shared-record
edit or descendant launch occurred. Only the leased note changed.

Unverified scope: runtime behavior, focused regression coverage, grammar-wide
source completeness, additional HIR constructors/internal bypass callers,
all downstream generic propagation invariants, full freshening/effect-hygiene
proof, termination, soundness/principality, exact public observer client
inventory outside the inspected cone, semantic admission and public F5 cutover.
The source-read method is independent of any supplied toy transition checker;
it is not independent validation of the implementation's source semantics.

**One recommended next action:** assign a bounded source-constructor migration
packet that maps the existing retained-expression producer fields to authentic
LocalSource/Call/formal inputs and their exact consumers, beginning with the
Apply `source_input=None` boundary. Retain the current constraints until that
bridge and focused coverage are established; then consider a separately
authorized implementation withdrawal. This recommendation does not select a
new construction or approve code changes.

## Frozen dependency snapshot

The primary supplied the commit baseline; this worker performed no Git reads
or mutations and therefore does not certify current HEAD/commit equality.
The following SHA-256 bytes identify the actual inspected dependency snapshot
for primary baseline comparison and independent review. Final reread matched
these hashes; no changed dependency hash was observed during that check.

| Dependency | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `crates/yu-solver/src/shadow_apply.rs` | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/candidate_call.rs` | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| `crates/yu-solver/src/shadow_f5.rs` | `b6a6c70da75329ff66cd9e6c0a2598a54cc8f0de7ba956f6f28b24616ca3a994` |
| `crates/yu-hir/src/module.rs` | `943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5` |
| `crates/yu-hir/src/shadow.rs` | `687b49061273974fe874a8479a8db91ba24cc77fe92e6d2b96ae46a3626cf9dc` |
| `notes/design/2026-10-10-simple-sub-legacy-withdrawal.md` | `93c2bf1c425522fdb41d0f4120d8430597a6091014741a64546e9fedb7bcf79a` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/progress/2026-10-10-simple-sub-legacy-withdrawal.md` | `150ce75b7d990017fdefb79998b68f0a74e8ba270ac4aff045deab423d0fdeed` |
| `notes/progress/2026-10-10-candidate-closed-lifecycle-retirement.md` | `0562bbe118f252bcd52a0708179313d6455639ecd50661850f5749463798c246` |
| `notes/progress/2026-10-10-candidate-unused-draft-withdrawal.md` | `cc2f9c5c69a94a041d35361291880264443023aafa0d932bfc74ae04dbb08e0e` |
| `notes/progress/2026-10-10-unused-observer-call-inventory-retirement.md` | `3db055e7b0f1dca75b1d38472b33c544f600efea163a1073d6eae818a6591ad1` |
| `notes/progress/2026-10-10-value-entry-effect-integration.md` | `4eec8de547631155b0e5f5c11a087bd7afc83780ea777bbb4da15b2789941145` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-13-candidate-fallback-withdrawal-owner-audit.md`.
- Baseline: `3e489f7ac9507023d0901bf882d68375529334c6`, primary pinned.
- Dependency hash changes: none observed between the two recorded snapshots;
  primary commit-baseline equality remains to be checked.
- Claim/review status: frozen bounded source characterization; independent
  `spec_auditor` PASS with no findings; no theorem closure, retirement claim or
  production authority.
- Checks already run: target absence; exact source branch/field/consumer reads;
  dependency SHA-256 snapshots. No tests/builds/probes/measurements.
- Proposed message: `research: audit candidate fallback constraint owners and withdrawal boundary`.
- Shared deltas intentionally left to primary/curator: link this audit from
  `tasks/current.md` if adjudicated; distinguish the adapter's live constraint
  role from historical closed consumers; retain complete migration and F5
  gates OPEN at the authentic source/Call constructor bridge. No shared index,
  authority, theory or question record was changed.

## Primary review and disposition

Independent `spec_auditor` review passed with no findings. It checked the
Authoritative withdrawal policy, the actual producer/dispatch/consumer
distinction, and preservation of source, Call, effect, scope, and generalization
obligations. The reviewer confirmed that graph SCC and incoming-use dispatch
return through live graph owners before legacy closed consumers, while fallback
facts/recipes still reach live propagation. It accepted the unresolved
`ApplySourceInput`/formal-name construction boundary as a migration dependency,
not proof that the fallback is obsolete.

Review scope: bounded source characterization and withdrawal-policy
conformance. Runtime behavior, grammar-wide coverage, downstream proof
invariants, observer clients outside the identified cone, and public cutover
remain uninspected. The fifteen dependency hashes match this frozen note. No
tests, builds, probes, measurements, or Git operations were part of review.

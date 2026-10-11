# Native conflict reflection and result-consumer crosswalk

Status: unreviewed research characterization; frozen for review on handoff
Baseline: `e899d1acd0f40b3b29b9f651f6cb658be316fbc1`
Method: bounded static source/implementation crosswalk
Lease: this file only; no compiler, test, shared-record, or Git changes

## Objective, authority, and claim boundary

Locate native conflict producers, source constructors, replay/lifecycle routes,
diagnostic consumers, and result consumers. The inspected code establishes
that semantic conflicts can coexist with completed private observations. It
does **not** establish an accepted public typing for contradictory source, nor
does it prove universal conflict reflection or public rejection.

Governing sections are the Authoritative top-level inference principles §§1,
4–5 and Authority/integration; `rules/compiler-engineering.md`, Deterministic
Simple-sub inference and Natural compiler behavior/proof-obligation economy;
private candidate suspension contract §§2–5; and contextual attachment/admission
design §§4–6 for successful paths. Full restoration/retry clauses are read
under the newer top-level principles. Deterministic no-search inference,
useful diagnostic continuation, no incorrect accepted typing, and no
inconsistent publication are fixed decisions. No blanket rollback premise is
introduced. The callback result is retracted; `my ans: [E] int` is not an
Oracle witness.

The existing type-error rejection audit remains the direct source witness
reference. This crosswalk extends its owners through freshening, intrusion,
contextual discharge, local publication and result APIs; it does not repeat
its Oracle attack. No Oracle checkout, executable oracle or checker was run.

Claim classes:

- **Established static facts:** the branches and API guards listed below are
  present at the pinned source hashes.
- **Bounded characterization:** these inspected routes preserve and publish
  diagnostic observations under their successful construction/drain premises.
- **Conditional derivation:** a generated fixed-head incompatible pair that
  reaches dispatch, diagnostic settlement and replay produces a solver error
  when allocations/identity checks succeed. Reachability of every original
  source contradiction is an additional premise.
- **Open A obligation:** every accepted public typing must exclude a
  source-generated contradictory obligation, including obligations transported
  or resumed through successful lifecycle paths. This artifact does not close
  that obligation or authorize a production implementation.

## Conflict producers and source qualification

| Producer | Actual condition and disposition | Source bridge and limits |
| --- | --- | --- |
| `lib.rs:11167–11231`, collected-fact admission | `ConstraintStore` returns `CrossKind`; appends `SolverError::CrossKind` and records component IDs, then continues. | Current Integer/Unit/Name/Lambda/Apply planning uses separately typed Value and Effect endpoints. No ordinary source constructor yielding this malformed cross-kind obligation was established here. Synthetic malformed-batch tests cannot supply that premise. |
| `lib.rs:12376–12391`, `dispatch_live_item` | `incompatible_value_shapes` identifies a terminal pair; records a direct witness in the typed memo and returns `Ok(())`. | Native literal rows, annotation checks, Function demands and Function child decomposition can meet here. The producer records a diagnostic fact; it does not fail the private inference session. |
| `candidate_effect.rs:604–657`, `candidate_effect_mismatch` | Retains a conflict for Contribution/AnnotationMember versus a closed Allowance or EmptyNegative; returns normally unless availability fails. | `candidate_check_effect_operand` at `:888–956` expands Support members/tail and compares resolved identities against the allowance, forwarding to its tail when present. An unmatched member in a closed allowance conflicts. `candidate_effect_contribution` at `:864` is `cfg(test)`; its use cannot alone demonstrate a source-generated Contribution. Production source effects can instead reach this owner as AnnotationMember from retained operation/interface or annotation views. |

`incompatible_value_shapes` (`lib.rs:14047–14073`) explicitly lists nine
fixed-head cases: Int/Function/Unit versus negative Bottom, and every unequal
pair among Int/Function/Unit. Positive Bottom and negative Top are permitted;
row endpoints defer to bound propagation. Merely observing a Function endpoint
does not establish a clash. Source reachability of negative Bottom in every
listed combination was not established.

The native source constructor chain is source-owned rather than inferred from
the error vector:

1. Opt-in `module/local_source.rs:295–325`, `:477–559`, `:663–675` constructs
   Lambda, Apply, integer and Unit nodes. Operation resolution is retained at
   `:600–627`; expression ascriptions at `:507–518`.
2. `CandidateInference::solve` (`shadow_apply.rs:79–113`) preflights retained
   source, tolerates only matched ordinary UnsupportedExpression placeholders
   and matched declaration placeholders, collects candidate mode, and runs
   the private session. Unsupported or unrelated HIR errors fail preflight;
   tolerated placeholders are not evidence that ordinary HIR admitted Apply.
3. `candidate_source.rs:336–350` emits positive literal <: Value row <:
   negative literal and pure computation-effect constraints. `:374` onward
   records source Apply operands and checking provenance. Actions at
   `:662–683` invoke the actual fact, Lambda, Apply, module-use, local-use,
   operation and annotation owners.
4. `shadow_apply.rs:1300–1405`, `admit_candidate_fact`, constructs the
   negative Function demand from the actual argument/result/effect endpoints
   and drains the callee demand. `candidate_effect.rs:1202–1274` constructs a
   written annotation's checking upper and exposed positive interface, checks
   the value/computation effect, and links the exposed interface to its target.
   Formal checks are paired links at `:1073–1113`; local annotation publication
   has its own source-action substage (`candidate_source.rs:649–655`).
5. `candidate_operation` (`candidate_effect.rs:786–803`) builds the resolved
   operation signature. `candidate_signature_effect` (`:1447` onward) creates
   operation-family Support views, annotation Support/Allowance views and
   symbolic tails with source-owned owner/position data. These are the actual
   potential source producers for effect-member clashes; this audit did not
   derive a complete source-level effect mismatch example.

Source annotation preflight (`candidate_source.rs:85–132`) remains a bounded
private envelope: concrete contravariant rows and multiple symbolic effect
variables are not generally admitted. No Catch constructor or handler
correspondence is established by this trace.

## Propagation, activation, and diagnostic consumption

| Route | Inspected implementation evidence | Exact premise still needed for universal reflection |
| --- | --- | --- |
| Value/Effect bound accumulation | `candidate_extrusion.rs:808–863` chooses the level-directed bound owner, inserts it, and calls opposite replay. `:763–805` rereads canonical opposite bounds, records Value diagnostic edges and creates contextual replay children. | Every semantically required source comparison must remain represented by these bound fibers/children. No universal incidence theorem follows merely from the loop. |
| Function dispatch | `lib.rs:12330` onward shares one typed worklist. Terminal witness production precedes ordinary structural/bound processing. Canonical rewrites and structural copies retain diagnostic child edges. Argument/result ports follow the Function dispatcher. | Complete source-to-four-port generation and all pending Call obligations are separate source/Call gates. |
| Contextual receiver checks | `candidate_context.rs:2733–2806` transports the actual relation and executes retained zero-word filters before endpoint dispatch. Existing allowances gain the current source origin and replay; otherwise the effect task installs the allowance. Discharge is recorded after those checks. | Zero-word/filter recognition, complete allowed-set evidence, and supported cycle recognition must be independently established; the code's discharged marker cannot prove its own premises. |
| Replay generation and consumption | `candidate_context.rs:2913–2988` combines new lower/upper fibers once, retains both parent dependencies and ordered children. Incoming fresh uses deliberately reset the replay frontier to own diagnostics. The child operation and typed drain retain their cursors. | Generated replay progress is distinct from completed child consumption. All suspension/recomputation paths still need source-qualified evidence; a successful synthetic cursor test is insufficient. |
| Intrusion equality | `candidate_intrusion.rs:513–605` merges an actual retained parent/copy pair, moves both bound sides/origins, canonicalizes fibers, advances intrusion generation, reopens a supplied Value diagnostic root and replays merged lower bounds. | This is representative-change handling, not complete certificate lifecycle validity. Eligibility of every source parent/copy merge and completeness of invalidation remain separate premises. |
| Equality and fresh-use transport | `candidate_context.rs:3125–3154` retains Derived edges for equality canonicalization. FreshUse records Transport provenance without a semantic replay edge. `:2284–2339` explicitly distinguishes the two. | A fresh-use conflict must not flow back into the template or a valid sibling. Omitting that upstream edge is deliberate; a theorem quantifying over provenance as though every edge were a subtype constraint would be false. |
| Memo activation | `lib.rs:11453–11474` reopens Value roots and checks native pair completion against the actual processing relation and intrusion generation. `:12950` preserves earlier diagnostic children when replacing a memo. | Intrusion generation does not certify lifecycle-generation readiness. The accepted design separately requires every certificate-dependent observation to register and withdraw before reuse. |

Value diagnostics are consumed by `complete_diagnostic_delta`
(`lib.rs:13099` onward), which builds scratch reverse edges/SCCs and settles
root witnesses from direct and completed-child seeds. `replay_witness`
(`:13721–13740`) projects the settled incompatible shape to the driving
occurrence/cause. `report_solver_kind` (`:14085–14130`) deduplicates by
occurrence and kind, appends `SolverError`, and returns `Ok(())`.

Effect conflicts use a different retained owner. `candidate_replay_effect_conflicts`
(`candidate_effect.rs:659–721`) walks actual contextual semantic children from
both raw and canonical initial pairs, reports each reachable retained conflict
under the driving occurrence/cause, and does not walk Transport as a semantic
upstream edge. Native typed drain Diagnostics (`lib.rs:12295–12309`) invokes
effect replay, Value settlement/witness replay, clears temporary scratch and
continues to acknowledgements. These consumers publish diagnostic observations;
none is an acceptance classifier.

## Freshening, source continuation, and publication consumers

`Graph` (`candidate_scheme.rs:35–48`) retains nodes, rows, bounds, contextual
evidence and attachment data. It has no conflict-free validity field.
`route_candidate_graph` (`:947–963`) consumes a stored root, recaptures its
current live graph and instantiates it. `freshen_candidate_graph` (`:965`
onward) reconstructs rows/terms/views and imports evidence; each bound's
original orientation and provenance are transported once by
`begin_candidate_fresh_bound` (`:1221–1266`) and restored/replayed at the fresh
occurrence. `instantiate_candidate_graph` (`:1268–1313`) publishes a FreshRoute
after the route succeeds in the availability sense. No conflict-absence guard
appears in that inspected publication.

Local results have the same distinction: `install_candidate_local_term`
(`candidate_scheme.rs:1319–1340`) stores a live LocalScheme after identity and
slot checks; `route_candidate_local_run` (`:1354` onward) captures/freshens it,
owns the cursor and eventually publishes its local route. Source `Install`
and LocalAnnotation separate construction from PublishLocal in
`candidate_source.rs:638–655`. These mechanisms retain continuation progress;
they do not classify a conflict-bearing value as a valid source typing.

The approved certificate lifecycle remains a distinct bridge. Current
`candidate_context.rs:2260–2339` has a **synthetic** source-support registration,
wait and Function-port invalidation path. `candidate_source.rs:34–58` explicitly
labels its wait/test adapter as neither an authenticated certificate nor
production readiness. Local pause injection is also test-only
(`candidate_scheme.rs:1346–1360`). The suspension contract §§2, 4–5 requires
Complete-only handoff, retained accepted edges, every dependent observation's
withdrawal and SCC group publication only after all work completes. Reading
these requirements is not evidence that all production owners enforce them.

| Publication/result consumer | Guard established by inspection | Guard not established |
| --- | --- | --- |
| SCC graphs, `candidate_scheme.rs:842–914` | Execute member actions, capture all member graphs, account storage, publish the staged group together. | No `self.errors` guard; the comment “Every member graph is valid” denotes the constructed private graph boundary, not a proved conflict-free source typing. Complete authenticated lifecycle readiness is separate. |
| `run_candidate` / `finish_candidate`, `lib.rs:10361–10376` | Execute succeeds; no closed arena and no legacy schemes; freeze CandidateSolvedResult. | No semantic-error emptiness or public source-admission certificate. |
| `finish_observations`, `lib.rs:17304` onward, `:17523–17571` | Builds projections and transfers errors/store/candidate graphs to frozen data. | Projection shape is not guarded by conflict absence. Diagnostic data and graphs coexist. |
| `CandidateInference` conflict/export/fresh-use/Call APIs, `shadow_apply.rs:119–184` | Export verifies root ownership and graph slot; fresh-use verifies occurrence ownership; source Call validates retained artifact. | Explicit unresolved source admission, complete Call, generalization and Function interpretation; candidate conflicts explicitly never establish source rejection. No public SolvedModule conversion. |
| `CandidateInference::effect_conflict`, `shadow_apply.rs:165–178` | Borrows branded retained operand/annotation identity and source provenance. | A diagnostic observation is not an accepted-result witness. |
| Ordinary `SolvedModule::solve` / `finish`, `lib.rs:17601`, `:17267–17300` | Genuine closed arena/finalized schemes required; errors are retained separately. | `Ok(SolvedModule)` is not guarded by an empty error slice. Source acceptance policy at an external caller is outside this lease. |
| Ordinary projection/root APIs, `lib.rs:17659–17715` | Artifact/root identity and finalized arena lookup. | Neither checks HIR/solver diagnostics to certify whole-source acceptance. |
| `CandidateValueObservation::solve` / export, `shadow_apply.rs:503–579`, `:688–699` | Preflights its narrower source carrier and uses ordinary closed F5 observations. Export delegates to root lookup and shadow closed scheme. | Every semantic premise is explicitly unresolved; conflicts do not establish source rejection. This is distinct from native graph inference. |
| `shadow_f5::ClosedSchemes::for_root`, `shadow_f5.rs:200–220`; source crosswalk exports in `shadow_candidate_source_crosswalk.rs:98`, `:269`, `:494` | Borrow exact existing root/scheme ownership and retained Call/Name incidence. | Identity/crosswalk agreement does not classify a semantic conflict or type an Apply. |

`shadow_initialization.rs:65–71` does inspect an empty HIR-error slice for one
exact initialization candidate envelope. That local source-shape predicate
does not consume native solver errors or establish general accepted typing.
No production rejection/acceptance consumer of `candidate_conflicts` was found
in the inspected solver owners; external compiler/CLI consumers were excluded
by the read lease and are explicitly unverified.

## Discriminating evidence and exact missing owner

The retained source test `source_call_registered_root_survives_conflicting_apply`
(`shadow_apply.rs:1642–1661`) constructs
`my apply f = f 1; my bad = apply 1`, obtains `Ok(CandidateInference)`, asserts
nonempty conflicts, and still observes both source Calls. This is a useful
source-qualified *private completion* witness through a module fresh use; the
test was inspected, not run. Its contradiction is the ordinary generated
Int-positive lower meeting the negative Function demand inherited from `f 1`.
The existing audit supplies the smaller direct integer-callee derivation.
Neither witness establishes accepted public typing.

The test `candidate_lifecycle_retirement_keeps_borrowed_effect_handles...`
(`shadow_apply.rs:1560–1584`) manually inserts a `cfg(test)` Contribution and
conflict after source execution. It establishes intended branded diagnostic
observation, not source generation of that effect contradiction. Likewise the
late Call-conflict tests in `tests/deferred_call_constraints.rs:233–295` manually
bridge constraints; they discriminate delayed propagation but assume their
transition inputs. They cannot supply a universal source bridge.

The smallest missing owner is the **successor accepted-result construction
and consumption boundary**, joining (a) completed source/constraint obligations,
(b) current lifecycle validity, and (c) semantic conflicts before a private
graph becomes usable accepted public typing. The present native
`finish_candidate` → CandidateInference export chain supplies observation
identity and errors, without that acceptance evidence. A separate upstream
obligation is complete source-to-conflict reflection; an empty diagnostic slice
alone cannot certify obligations the source planner never generated.

This documented gap prevents promoting the inspected candidate completion
claim to a universal accepted-public-typing theorem. It is not a counterexample
to such a theorem: no actual accepted public typing with a source-generated
contradiction was established. Do not repair the proof by assuming conflict
absence from `Ok`, treating suspension as source rejection, requiring immediate
fail-on-first-conflict, or restoring blanket rollback.

Recommended next action: assign the accepted-result owner one bounded packet
that pins the real successor acceptance constructor/consumer and states its
required source completion, current-generation validity and semantic conflict
premises. Keep source reflection and accepted publication as separate open
premises, and preserve useful diagnostics on rejected/affected private work.

## Checks, coverage, resources, and dependencies

Checks: read-only `git rev-parse HEAD`, initial `git status --short`, bounded
`rg`, `sed`/`cat`, and SHA-256 capture; final baseline/dependency recheck. No
build, tests, Oracle run, checker, search seeds/ranges, mutation or measurement.
One sequential lightweight shell process at a time; zero heavyweight processes.
Peak CPU/RAM and exact wall time were not measured; the packet's 30-minute cap
was the stop budget. Some initial broad captures truncated, including the
large task record and combined searches; decisive owners were reread narrowly.
No whole-task-record completeness is claimed.

Omissions: all-source soundness/principality, complete Call, Catch/handler
meaning, arbitrary mixed contextual cycles, authenticated production
certificate creation/invalidation/recomputation, every abnormal route, external
CLI/backend consumers, and executable confirmation. This static crosswalk
shares source/constraint assumptions with existing tests. It has no independent
runtime oracle, and source code describing its own transitions is evidence of
implementation behavior rather than proof of those transitions' semantics.

Frozen dependency SHA-256 values:

```text
943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5  crates/yu-hir/src/module.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94  crates/yu-solver/src/lib.rs
6bea8808153b8b71a57e4a8583284e49284ec9aa35118a61f44a3a387a8a32f6  crates/yu-solver/src/shadow_apply.rs
13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49  crates/yu-solver/src/candidate_source.rs
fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0  crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df  crates/yu-solver/src/candidate_effect.rs
4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987  crates/yu-solver/src/candidate_context.rs
9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1  crates/yu-solver/src/candidate_scheme.rs
b6a6c70da75329ff66cd9e6c0a2598a54cc8f0de7ba956f6f28b24616ca3a994  crates/yu-solver/src/shadow_f5.rs
e17ab376c46575fc780fe79412cedf147cce7542b8e7ea2f8e09017db360bd10  crates/yu-solver/src/shadow_candidate_source_crosswalk.rs
2c90286d87c9f16d579153b1ef8e1bb4e5f586e71f65aa6d28552d582b6d3411  crates/yu-solver/src/shadow_initialization.rs
ff3a879f375763f6310b0a7d1e7509ae9e66386d42fd39cc18beb5adddca6327  crates/yu-solver/src/tests/deferred_call_constraints.rs
edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389  notes/design/2026-10-11-yulang-inference-top-level-principles.md
734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d  notes/design/2026-10-11-private-candidate-suspension-contract.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
e88afa0248a780cdf8d38fc3b1ad7950dd24596e2b301ebf03bd9b5678e41175  notes/progress/2026-10-11-simple-sub-type-error-rejection-audit.md
```

## Commit packet

- Exact leased path: `notes/progress/2026-10-11-native-conflict-consumer-crosswalk.md`.
- Baseline SHA: `e899d1acd0f40b3b29b9f651f6cb658be316fbc1`.
- Dependency changes authored: none; hashes above pin the inspected dependency
  set. Any subsequent source change needs a dependency-scoped recheck.
- Review status: unreviewed bounded characterization, frozen at handoff; no
  independent review, theorem closure, production conformance or adoption claim.
- Checks already run: static producer/consumer/lifecycle trace, initial clean
  baseline check, dependency hash capture and final hash/baseline recheck;
  no runtime checks.
- Proposed checkpoint message: `research: map native conflict reflection and result consumers`.
- Shared-record deltas left to primary/curator: preserve separate OPEN owners
  for source-to-conflict reflection, authenticated lifecycle readiness and
  accepted public-result validity; record that candidate completion/identity
  exports supply observations rather than accepted typing. No task/index/
  authority or question-board edits are included.

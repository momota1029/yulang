# R89 source handoff — revision 2

Outcome: **bounded constructor incidence established; original supplier still missing; NO_SAFE_CODE_SLICE**. Research-only source evidence, pending independent review. This report gives native producer equations, not a complete original App derivation, a source counterexample or A/B closure. No Rust edits.

## Assignment, pins and resources

- Sprint `EFFECT-PERMISSION-APP-DEMAND-INCIDENCE/20261101-R89`, contract revision 1; contract SHA-256 `c036d191f2748d971862aab638ac92bd7147ac8ff27289a68e35ed1d7c23e45b`.
- Initial manifest SHA-256 `86727cb01dc42a4b51148e1dff9c75a4f37af01c7862a56afa18eed25ca2a256`; all **33** input sizes/hashes matched at entry. Amendment 01, commit `e33db399d6a8f690d347bbf1b59b09c229472b57`, admitted the 34-input revision-2 manifest `effect-permission-app-demand-incidence-20261101-r89-inputs-r2.json`, SHA-256 `6fe8973a6b5e1aa55d73bb47c85cf4bb11b9a57e1a8b034a167197e7f8697dfa`; **34/34** matched on amendment entry. Amendment receipt SHA-256 `1ea4840118c7ce0a2f6d8ca96b528d7a833f639fa2e694a35c7705fc64dcda20`. Final recheck is reported separately with the artifact hash.
- Admission commit: `4781d06dac7abcc11f8537523bbc4a833adcbf65`; manifest source-baseline field: `e56d1b618c2025859f5ab912d7ba3168634aaaed`. Exact manifest bytes govern this investigation, including its explicit dirty inputs.
- Actual worker/author: `/root/r88_source`, resumed by `/root`; session R89. `/root/r89_source` was a planned alias, not the observed worker. Requested source lane: Luna/high in the contract; observed runtime model/effort **UNKNOWN**. No children, coauthors or delegation.
- Sole output/lease: `tasks/agent-loop/inbox/effect-permission-app-demand-incidence-r89-source.md`. No other writes, scratch, caches, environments or `/tmp` output. Frozen after creation; writes stopped before review.
- Source envelope: 1,000 seconds. First observed clock: 2026-10-31 15:01:35 UTC. Amendment's incremental Graph inspection started at 15:08:57 UTC, capped at 300 seconds within the same envelope. Core read/findings finished before 15:10:12 UTC (75 seconds); report integration/submission time is given separately. No tests/builds/Cargo/Lean/Lake, heavy process or executable model. Exact process CPU and peak RSS UNKNOWN; command-reported shell durations were below one second. No budget reset.

Exact Rust SHA-256 pins:

| Path under `crates/yu-solver/src/` | Frozen SHA-256 |
| --- | --- |
| `candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `shadow_apply.rs` | `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff` |
| `candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` |
| `candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `candidate_value_graph.rs` (Amendment 01 only) | `aaaa88a374083f898188cd390b8cf0244855d8c09c8939b9e68ee2831bc692cf` |

Admission-commit `candidate_source.rs` and `candidate_call.rs` agree with those pins. Admission `shadow_apply.rs` is 275,872 bytes / `2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d`, whereas the frozen input is 276,524 bytes. Its dirty delta is a cfg(test) trace hook and two test-structure fields; it is not a complete Call supplier. Admission `candidate_context.rs` is 265,078 bytes / `962af7c44b2e57ba50b7738e82785bd68b517e881ba08ea41c544c9314d60021`, whereas the frozen input is 265,778 bytes, retaining borrowed Internal-use origin/drain fields as recorded in R88. Narrow status marked both modified. These existing changes were preserved; no test source was edited or executed. Observed HEAD during baseline comparison: `91c94044bd485ec50959368e3483a53e6032c9eb`; it does not replace the admission baseline.

Authority remains original preservation §§1, 5, 7; immutable birth-level decision §§2–4, 6; Source-Generalize decision §§2–4/construction §§3.1, 3.3, 5.1–5.2; top-level principles §§1–5. The R88 reviewed obstruction is the prior result; its errored Lean declarations are not accepted proofs. Every theorem/local-law argument keeps its original source domain and scopes.

## Constructor derivation with explicit hypotheses

These are code-reading consequences of the actual assignments. Hypotheses: `emit_candidate_source` successfully processes the original owner-borrowed LocalSource; its App action reaches `admit_candidate_fact` with consistent recipe/source-input indices; required allocation, ownership and provenance operations succeed. Statements about `ScopedDemand` additionally require `scoped_enabled`, the retained by-occurrence entry, and a `Some` introduction. They do not assume or conclude source typing or successful solving of the demanded constraint.

Let `o` be the HIR App occurrence, `i` its owner-local expression index, `r` the recipe index and `c` the call index. Let `C,A` be the retained callee/argument CandidateEndpoints; `ec,ea` their effect component positions; `v,eapp` the App result/effect positions.

1. `candidate_source::emit_candidate_source` authenticates the original LocalSource by pointer, source root/receiver and HIR ownership (`candidate_source.rs:1044–1073`). Its App Finish branch (`1808–1924`) obtains all coordinates from that same source expression and children, sets `r = candidate_recipes.len()`, retains

   ```text
   CandidateRelation::Apply(C, ec, A, ea, v, eapp)
   calls[c] = ApplySourceInput(owner,i,calleeIndex,argumentIndex,level,r,
                 C,ec,A,ea,v,eapp,checking=(o,0),cause=for_occurrence(o,0),...)
   recipes[r].source_input = Some(c)
   Action::Candidate(r)
   ```

   `retain_candidate_relation` initially creates source_input=None (`shadow_apply.rs:3704–3740`); this source constructor explicitly fills the reciprocal index. Scoped collection also inserts `by_occurrence[o]=c` with duplicate rejection and registers `InputRouteId(c)` in the App's lexical region.

2. `execute_candidate_action(Action::Candidate(r))` clones that recipe and calls `admit_candidate_fact` (`candidate_source.rs:2479`). The latter checks `input.recipe`'s retained recipe, occurrence, source-input backlink, both endpoint variants/indices and four component positions (`shadow_apply.rs:3966–3991`). In scoped mode, `authenticate_scoped_apply` also authenticates a Local callee's exact retained local route, slot, scheme identity and `authentic_use_instance`; this checks native route provenance, not original source legality.

3. Write `val+(C)`, `val+(A)`, `val-(v)` and `eff±(p)` for the actual live terms constructed by these helpers. With graph effects enabled, the Apply branch allocates a fresh invocation row `j` at the **current canonical application row's level** and constructs (`shadow_apply.rs:4105–4179`):

   ```text
   demand = NegativeFunction(val+(A), eff+(ea), eff-(j), val-(v))
   native = {callee=val+(C), argument=val+(A), callee_effect=eff+(ec),
             argument_effect=eff+(ea), result=val-(v), demand,
             invocation_effect=eff-(j), invocation_row=j,
             application_effect=eff-(eapp)}
   ```

   The two uses of “result effect” must be disambiguated: `CandidateRelation::Apply.result_effect` is the whole **application** effect component; the demand Function's ResultEffect is the fresh **invocation** effect `eff-(j)`. The argument-evaluation effect is the demand's ArgumentEffect. None is the value result.

4. If `formal_name=Some(n)`, the producer follows `names[n].registration=k`, `formals[k].owner/lambda`, then the actual owner's LocalSource Lambda occurrence `l`. Only `omitted_formals[l]` supplies the optional record (`4147–4172`):

   ```text
   introduction = Some({registration=k,name=n,omitted=clone(omitted_formals[l]),
                         checking=(o,0),cause,demand,
                         field=ResultEffect,effect=eff-(j),row=j})
   ```

   Otherwise introduction=None. These fields and `native` are installed **before** `admit_and_record_provenance` and `constrain_live_value`; a later failure does not retrospectively turn them into a successful Call receipt. `source_call()` itself has no errors guard (`shadow_apply.rs:2100–2110`).

5. Admission records the exact slot-0 value comparison `val+(C) <: demand`, then separate effect comparisons (`4181–4250`, `4267–4290`):

   ```text
   slot 1: eff+(ec) <: eff-(eapp)
   slot 2: eff+(j)  <: eff-(eapp)
   ```

   It does not directly add `ea <: eapp` in this Apply branch. `ea` is retained inside the demand for the actual argument protocol. This derivation does not assert that that protocol implements the complete original inert-carrier/Force law.

6. At the first inspected context consumer (`candidate_context_seed`, `candidate_context.rs:3794–3857`), slot 0 and `Some(introduction)` produce exactly

   ```text
   ScopedDemand {original_call:c,use_instance:0,root:demand,
                 output_scope:computation_scopes[o],input:InputRouteId(c)}
   ```

   Slot 2 independently reads this App's actual source argument occurrence and carries `release(computation_scopes[argumentOccurrence])`; it does so even without an introduction. The native source-event set is separately selected by `references.checking[(o,slot)]`; that is not the same field as `original_call` or the lexical scope number.

This establishes an owner-local, conditional **native construction equation** connecting recipe, source carrier, negative Function, optional omitted-formal evidence and scoped consumer. It advances R88's previously uninspected producer edge. It does not yet map those coordinates to a single original semantic App witness.

## What the provenance observer actually checks

`candidate_call::observe_inner` (`487–682`) reselects the owner's actual `Form::Apply`, checks child indices, checking occurrence/full cause, HIR ownership and `scope_owned` for App and children. It checks all four demand ports and their native kinds/polarities, and the invocation row ordinal. For a formal route it follows only permitted source wrappers to the resolved same parameter Name/Lambda, checks source roots/scopes and the positive native registration root. With an introduction it checks the omitted owner/Lambda/formal/source position/AnnotationScope, registration/name, checking/cause, demand, field=ResultEffect, invocation effect and row.

The actual producer clones the exact omitted-formal Arc; the observer checks its fields, not equality against the source map's Arc pointer. `scope_owned` establishes owner-local validity; it does not construct the complete original event/type dependency telescope. `NativeInterface.callee` is a native type term, not the actual returned runtime Value/provider. The positive parameter registration root is not by itself the original whole registered interface.

Formal registration and omission have real source suppliers: `candidate_source.rs:1106–1118` records owner, Lambda expression index, parameter, recipe position, role and AnnotationScope; `1162–1177` records resolved parameter Names; `1282–1297` creates OmittedFormal only for an unannotated, non-unit, non-record-pattern formal. `initialize_candidate_source_levels` (`2292–2329`) checks the parameter recipe and installs its positive native root once; Computation role gets a separate entry-effect row. These are registration/omission identities. They do not supply a formal's complete original introduction, admission, checking-exposure or seed-exposure laws.

## Absent introductions, annotations and a discriminator

| Branch | Actual behavior / scope limit |
| --- | --- |
| No `formal_name` | Native demand/interface and slot-0/1/2 comparisons still exist. No DirectionalIntroduction; slot 0 adds no ScopedDemand. Ordinary module/result/local callees are not declared unprotected by this None. |
| Annotated formal | OmittedFormal is not constructed. Observer accepts None for an otherwise authenticated annotated formal; role derives from whether the outer annotation has effects. FormalEntry/FormalAnnotation actions remain (`1323–1342`). None is not a language-wide effect judgment. |
| Unannotated unit/record-pattern formal | Constructor omits OmittedFormal too. A missing introduction with an otherwise retained unannotated formal route makes this diagnostic observer unavailable; it does not prove that the ordinary source program is rejected. |
| Some introduction | Requires actual omitted-formal map entry at the producing Lambda. Observer rejects annotation/unit mismatch and all listed field mismatches. No original role/admission theorem follows. |
| No scoped mode/by-occurrence entry | Context seed retains its ordinary relation but adds no scoped App demand/transformer from this lookup. |
| Graph effects disabled | The generic Apply branch uses bottom/empty effect leaves; a Some source_input then needs the absent invocation row and fails before native installation. This is a candidate-path condition, not a new language restriction. Generic recipes with no source input are separate. |

Written expression Ascriptions propagate the inner formal route and endpoint while retaining an `Action::Ascription` with the actual annotation, occurrence, level, effect and source scope (`candidate_source.rs:1925–1961`). Group/block final expressions likewise propagate the formal-name route. Those aliases do not discharge the original annotation boundary. In the original builder, annotation premises are outside the App's ViewLogic witness; the required HIR-to-original-scope correspondence is still missing.

A discriminating **syntactic derivation**, without an executable or source-admission claim: original `singletonFormalCall` requires two bare unannotated formal Names, a single-use Value callee and a Value argument. For App(formal Name, literal), it computes false. Native introduction selection checks the omitted callee formal and has no argument-Name or single-use test. Thus, if that source constructor path completes, it can produce Some introduction while the original App has no `roleAndInitialCallOrigin` atom. Wrappers further distinguish the two tests. Consequently DirectionalIntroduction cannot be identified with that original atom merely by its presence. This is not a counterexample to typing or the preservation theorem; no arbitrary Kernel or accepted-source witness was manufactured.

Scoped collection itself has opt-in availability guards (`1808–1864`, `scoped_result_callee:524–548`): several argument/callee joins, binder aliases and annotated/nonempty-block Local routes are deferred. Result-callee spines need the restricted source-grounded supplier. Limits are 4,096 records / 65,536 work, explicitly private availability limits. These cases remain in the original parent domain; this report does not promote the private envelope into language semantics or whole-source coverage.

## First missing original supplier and its dependent fields

The decisive missing supplier is now located at the transition from the retained registration/demand tuple to **original complete Call formation**. `candidate_call::PendingCallConstruction::suppliers` (`400–439`) is an explicit request interface, not such a constructor:

- For the omitted-formal path, the first prerequisite is `OriginalRegistrationWholeInterface`, then `ActualFormalIntroductionRoute` and `OriginalCheckingExposureAndSeedExposure`. The identity join in `shadow_apply.rs:4147–4172` supplies none of those original complete laws.
- Every source Call still requests `OriginalGenCall0`, `ArgumentReifyAndWholeCarrier`, and `ReceiverDispatchAndCompleteResultFutureInterfaces`.
- Direct module callees additionally request `ModuleNameSourceTypingAndAdmission` and `ModuleUseReceivingExportCorrespondence`.

Exact dependent formation coordinates remain the `OriginalGenCall0Input` list (`candidate_call.rs:252–286`): B, X, Xi, Delta, Declaration, ArgumentInterface, RegisteredRoot, CompleteDemand, Beta, CalleeLexicalUse, ArgumentLexicalUse, CallOccurrence, CheckingOccurrence, ImmediateOutputPosition, CompleteOutputPosition and ElimOrigin. These are names of missing original inputs; this report does not invent their semantics from scalar IDs. The native occurrence and endpoint counterparts above are partial construction evidence, not proofs that all original coordinates have been supplied.

Responsible construction owner: original source App/Call bridge at `shadow_apply::InferenceSession::admit_candidate_fact`'s Apply branch, consuming `candidate_source::emit_candidate_source`'s exact ApplySourceInput and the owning parameter registration. The diagnostic boundary is `candidate_call::PendingCallConstruction`; first context consumer is `candidate_context_seed`. Primary/Luna owns admission of the missing supplier packet. The fields needed next are the actual whole registered formal/interface; returned callee Value/provider; inert whole argument carrier/root/view; receipt/current/context/continuation/path/consumer/incidence; complete immediate/future output evidence; their original shared/environment telescope and annotation/permission dependencies.

Formally, `OriginalSourceGeneration.sourceRules` (`111–123`) requires one admitted `ScopedValue` under `⟨AppSite,viewLogic,0⟩`; **all** descriptorFormation, wholeArgumentCompatibility, completeCallCertificate, sourceCallIncidence, callableImage, any computed role clause, both checking derivations and both child SourceJudgments use that same extended original environment. Native four-port construction and omission identity do not construct that witness or those Local proofs. The argument side must be the original inert whole code interface, and the callee comparison uses its returnedValue port, not a guessed solved endpoint. `OriginalSourceInterpretation.CallInput` (`136–148`) retains actual value/root, event, context, continuation, carrier/root/view, receipt, path, consumer and incidence; none can be replaced by a native scope number. Kernel.atom/admitted and Inputs' actual admission/execution/checked-observation laws remain independent premises.

Therefore the repaired R89 App inversion, if accepted by its verification owner, can expose these precise goals. This source result supplies the constructor identities above only; it cannot instantiate the inversion with a complete original App derivation. R88's checker failure and R87's finite reader PASS are not original Call suppliers.

## Qualification, effects and publication/use boundaries

The source walk supplies birth/planning inputs: `references.retain_source`, `record_expression_level`, parameter `record_birth`, local initializer `record_birth` and binder births (`candidate_source.rs:1072,1089,1214,1285,1305,1387–1500,1554`). `CandidateIntrusionObservation` (`shadow_apply.rs:1193–1304`) exposes exact origin/receiver identities, source checking, row/polarity/target/occurrence/source-set parents and `references.qualifies`. The Graph implementation was initially outside the four-file lease and was not opened until committed Amendment 01; its newly inspected result is below. Native extrusion generation remains outside the read scope. Presence of an omitted formal is not birth qualification; `input.level` and the fresh invocation row's current level are not immutable Value birth.

For a scoped demand, `candidate_function_port_admit` (`candidate_context.rs:3925–3988`) authenticates the parent negative Function root, removes the demand from the child and constructs ArgumentEffect=`stamp_input(input)` and ResultEffect=`protect_body(output_scope,input)`. Argument/ArgumentEffect swap inherited context; Result/ResultEffect preserve it. Slot-2 release uses the actual source argument scope. These are separate retained native transformations. Their original complete Call interpretation still needs lower/upper support, annotation permissions, handlers/attachments, actual receiver/provider/captures, receipt, future/continuation and witness equations in that one source telescope. No effect meaning is changed or inferred from None.

Local initializer publication is traceable further than in R88: `Work::Install` adds the one-shot initializer effect to the enclosing block and emits Install/LocalAnnotation (`1558–1586`); `step_candidate_source` publishes through `install_candidate_local_term(slot,exposed,boundary)` (`2415–2421`), while Action::Local calls `route_candidate_local` (`2498`). Their implementation owners are outside the four pins. `ScopeInventory::owned/fresh` preserves the supplied capture forest and allocates scope/input origin remaps (`272–357`), and scoped Local authentication checks retained scheme-use provenance. These are concrete native hooks, not Source-Generalize's typed fixed-dependency closure, whole-component original frame allocation, Shared witness preservation or original new/alias partition. Original provider/capture identity and publication/use incidence remain explicit missing dependencies. Receiver residual publication is not reread or used to substitute for those suppliers.

## Amendment 01 — actual birth-qualified graph supplier

This sequential revision preserves the four-file derivation. Pre-amendment local revision 1 was 23,964 bytes / SHA-256 `3da8bd4fa852e41a806835e1e18bd5da19425e4b2451d431499829678efada71`; it had not been hash-submitted for review. The primary explicitly admitted the new read dependency and continuation on this same handoff. No frozen independent review target was modified. Only `candidate_value_graph.rs` production lines 1–398 and permitted in-file locators were inspected; no tests were read as proof or executed.

Actual construction, not a conclusion from `qualifies`'s name:

1. Semantic keys are `Value::{Module,Local,Parameter,CatchBinder,Expression}`. `intern` reuses the same ordinal for an equal key, records a separate reverse semantic identity table and starts Module birth at 1 (`48–73`). `record_level` accepts the same stored level, rejects a different stored level, and fills only None (`75–81`). `record_birth` does not invent isolated vertices for unused declarations. Resolved Names map to the original declaration key; they do not reset its birth at a later Name-use level (`83–115`). The actual source walk previously traced supplies the declaration birth and expression/helper planning level.

2. `retain_source` assigns the source root an identity and level 1, traverses source syntax with an owner ordinal, and changes ownership to the actual Local declaration at each nested binding initializer (`117–255`). It retains resolved Name reference edges from that owner, visits all listed source children and defaults, and builds separate helper fragment vertices for the selected Name/Apply/If/sequence/statement-block/tuple/record/variant forms (`256–332`). Helpers have no semantic Value descriptor; their source planning levels must subsequently be filled. This is a concrete extraction construction, not yet an independently proved equality with the original semantic Ref for every supported form.

3. For each actual `Form::Apply` (`333–345`), it interns the App expression result and its fragment/child-reference links, then records

   ```text
   receiver = intern(expression_value(source, calleeIndex))
   event = events.len()
   checking[(AppOccurrence,0)] = event
   checking_by_event[event] = (AppOccurrence,0)
   events[event] = {origin: owners[AppIndex], receiver}
   ```

   `expression_value` peels Group/Ascription; a resolved Name chooses the corresponding declaration Value; every other callee chooses its exact source Expression occurrence. It does not select a provider by a solved type or use the App result as a direct Name receiver. This supplies the precise App-checking-to-origin/receiver join that revision 1 could only name. `candidate_context_seed` selects that same event through its separate checking map lookup. The Graph event is associated with every retained App; it does not require a DirectionalIntroduction.

4. On a fresh complete partition, `seal` (`354–394`) rejects any missing planning level and any edge **into an auxiliary helper** whose source and target planning levels differ. It leaves cross-level edges in the raw forward/reverse graph. Its forward finishing-order DFS traverses an edge only when the two planning levels match; its reverse SCC DFS uses the same equality test. `qualifies(event)` (`395–397`) compares the recorded event endpoints' cached component IDs, returning false when either lookup is unavailable. This is actual equal-level filtering throughout the SCC walks; it is not the invalid global-SCC-plus-endpoint-birth test.

A bounded derivation from these loops: let H be the retained graph with complete level map ℓ, and H_= its edge restriction `ℓ(u)=ℓ(v)`. Subject to the ordinary two-pass SCC invariant and a valid fresh partition, the returned components are those of H_=, so a successful event comparison gives mutual paths that stay at one planning level. For projection through helpers, suppose the semantic Ref relation is exactly the helper-path expansion of the source incidences (an extraction premise, not assumed proved here). Every helper-entering edge is level preserving by the checked guard; hence a projected Ref edge whose semantic endpoints both have birth k expands wholly at k. Conversely, a helper-filtered path projects to same-birth Ref edges. Under that premise, the filtered native test agrees with the selected semantic G_k test. This conditional projection argument identifies the exact remaining source-extraction premise; a comment claiming helper preservation alone does not discharge it.

Lifecycle qualification: `seal` first returns immediately if `components.len()==edges.len()`. `qualifies` consumes the cached table without rechecking epochs or source extraction. Thus the calculation above requires the owning lifecycle to seal the complete current construction and preserve it until use; node-count equality alone does not certify absence of later same-size edge mutation. The external lifecycle/actual extrusion caller is not inspected in this amendment. No stale-partition bug or whole-history correctness claim is asserted.

Amendment result: source identity, immutable level assignment, actual App event incidence and equality-filtered SCC loops are now traced at their concrete supplier. This closes the **inspection omission** of revision 1, not the original source/native qualification theorem or any complete Call/effect supplier. Full Ref/helper adequacy, lifecycle application and actual extrusion parent/copy coverage remain open. The earlier missing OriginalRegistrationWholeInterface/Gen-Call-0 witness remains the first missing original semantic supplier for the App derivation.

## Coverage, checks, disposition

Method: constructive source-field derivation and local-rule obligation comparison. No semantic oracle, executable transition model, seed/range enumeration or mutations were run. This differs from a checker that assumes transitions: the equations were read from the producer assignments and checked against the consumer/observer guards. Oracle independence is limited to separate original source definitions versus actual Rust constructors; both still need independently established original local laws. A successful native metadata observer is not an independent source-semantics oracle or Call acceptance receipt.

Checks: bounded `rg`, `sed`, read-only manifest `pathlib`/`hashlib` validation, exact `git show` of the four admission blobs, narrow `git diff`/`git status`, and `git rev-parse`. All returned exit 0. No Git mutations. No whole-crate absence claim follows from these searches. Additional reads used only manifest-pinned theory/authority and the already supplied operating rules/skill. No uncommitted R89 proof proposal was consumed.

Unverified: original complete suppliers listed above; actual source-to-Lean binder/environment interpretation; full Ref/helper extraction adequacy and sealed-partition lifecycle; extrusion/native extraction and full transition coverage (including the external constrain_live_value/effect-to-seed call paths); annotation/effect proof application; actual scheme installer/allocator; joint lift and FiberConstant source construction; native progress/termination; whole-language soundness/principality; any R89 Lean checker/axiom result and independent review. Original A/B, Rust implementation and production remain OPEN.

Recommended next action: primary should freeze a supplier packet for the **original whole formal/interface and complete Gen-Call-0 formation** at this exact Apply producer, requiring its original carrier, returned provider, admission and complete output/future tuple in one telescope. The source identity and newly inspected qualification construction can be reused; adding another endpoint inventory does not supply the missing law. No Rust implementation slice is justified by this result.

## Commit packet

- Exact leased path: `tasks/agent-loop/inbox/effect-permission-app-demand-incidence-r89-source.md` only; submission SHA-256 supplied separately after freezing.
- Baseline: admission `4781d06dac7abcc11f8537523bbc4a833adcbf65`; manifest baseline `e56d1b618c2025859f5ab912d7ba3168634aaaed`; dirty source overrides explicitly pinned above.
- Dependency hashes changed by this worker: none. All existing dirty/quarantined paths preserved.
- Claim/review: research-only native constructor derivation and missing original supplier; independent review pending; no own-output certification.
- Checks already run: hash/size validation, bounded producer/consumer/declaration tracing, exact baseline blobs and narrow diff/status; no tests/build/Lean/Lake.
- Proposed checkpoint message: `research: trace R89 App demand construction to missing original Call suppliers`.
- Shared-record deltas left to primary/curator: record the now-established native producer equations and Amendment 01's inspected App-event/birth/SCC loops; keep their source-extraction/lifecycle premises and complete original suppliers, source/native joint lift, A/B and production OPEN; correct planned alias to actual `/root/r88_source`; retain baseline/dirty-byte distinction. No shared record was edited.
- Worker: STOPPED WRITING after creating sequential revision 2 under Amendment 01; no descendants or generated-output leases. Frozen for review; repair requires a new sequential revision directed by primary.

# F5 consumer migration boundary inventory

Sprint-ID / contract revision and SHA-256: `catch-consumer-and-f5-migration-readiness-20261016` / rev 1 / `4848ff79e71a391e24f576e5bad491c43be1591f01139a44495ffcdf36bc3b29`
Assignment-ID / handoff revision: `assignment-f5-consumer-migration-boundary` / 2
Prior frozen handoff: revision 1 / `a7a1bb926bc1d81ce5797dc8cb8bd0f0294d09c9b2b76bc8a92565c3a83356ab`; Luna acknowledged intake. This sequential delta supersedes no rev1 evidence except where explicitly extended below. Rev1 review does not apply to these changed bytes; fresh delta review is pending.
Parent gate / original scope: full inference and F5 replacement; original Call/effect H1/H2/JOINT_DEC, authentic source constructors, source/native correspondence, legacy withdrawal, and production cutover remain separate OPEN parents. This is an inventory only; no migration authority or theorem result follows.
Baseline: contract baseline `eeb7826a238848d219058f4f14e0948c115ae6ac`; this read-only checkout's pinned source SHA-256 values were checked against contract rev 1 and match.
Role / worker / runtime: requested `implementer`, `gpt-6-luna`, high. Actual worker identity/session/launch receipt and observed model/effort are unavailable here: UNKNOWN. I do not infer Luna execution from the request string.
Exact lease: `tasks/agent-loop/inbox/20261016-f5-consumer-migration-boundary.md` only. No compiler write lease. No descendants. No tests, builds, probes, Git, state/board/question edits, or other writes.

## Result

**NO_SAFE_CODE_SLICE** under the current authority. The smallest connected historical consumer is `CandidateValueObservation`'s root export plus its source crosswalk clients, including the retained current F5 closed-scheme lookup/fresh-use observations. The approved successor `CandidateInference` is available, but its outputs are candidate Value/Effect graph exports and graph fresh-use routes. No existing successor API supplies the old `CandidateExport` contract (`SolvedValue` plus `ClosedSchemeRef` / `ClosedValueSchemeView` endpoints), its matching closed definition-use observations, or their established source/native correspondence. A direct replacement would change the observable contract or silently assume the very correspondence that remains open.

This is not an argument to retain the retired Simple-sub bypasses. Historical observers and default inference still have actual F5 owners; their existence is a migration obligation, not approval of their old construction or proof that the successor is ready for cutover.

## Owner paths and caller contracts inspected

1. **Historical value observer owner — `crates/yu-solver/src/shadow_apply.rs`**
   - `CandidateValueObservation::solve` preflights retained `ResolvedExpr`/shadow-local shapes, calls `ConstraintBatch::collect_mode(hir, true)`, rejects internal SCC uses, then calls `SolvedModule::solve_with_shadow_fresh_capture`. Its private result therefore owns legacy F5 closed schemes. `export(root)` returns the legacy root value and `shadow_closed_schemes().for_root(root)`; `definition_use` returns target/receiving closed schemes and a current fresh-capture observation. All of these retain exact HIR/root/use identity and leave source typing/admission, complete Call, export transport and candidate semantic premises unresolved.
   - Actual call sites found: integration tests in `shadow_apply_candidate.rs`, `shadow_candidate_source_crosswalk.rs`, `shadow_candidate_multiroot_source_crosswalk.rs`, `shadow_candidate_call_formation_crosswalk.rs`, and the test-wired `shadow_candidate_source_crosswalk.rs`; plus local unit tests. Repository search found no non-test production caller of `CandidateValueObservation` outside its source-crosswalk helper. The integration tests are real historical clients, but are not production cutover evidence.
   - Caller contract that blocks substitution: callers consume `CandidateExport::{value,scheme,endpoints}`, exact per-use target/receiving schemes and fresh rows, candidate Call facts, and `CandidateSourceCrosswalk` joins. Successor `CandidateInference::export(root)` instead returns `CandidateGraphExport` over a candidate graph; `fresh_use` returns candidate graph rows. Type and semantic contracts differ.

2. **Closed F5 observer owner — `crates/yu-solver/src/shadow_f5.rs` plus `shadow_scc.rs`**
   - `SolvedModule::shadow_closed_schemes` and `ClosedSchemes::for_root` expose exact finalized current-root schemes. The observer explicitly says Q/R are scheme-local, not source binders, and successor correspondence / typed endpoint-profile association are unimplemented.
   - Under `shadow-f5` + `shadow-scc-observer`, `SccTopology::{use_closed_scheme,definition_closed_scheme}` joins retained current SCC/use identities to those finalized current-local schemes. Its API explicitly does not identify Q/R with successor interfaces or source slots. These are observer consumers, not the candidate successor's public scheme route.
   - Actual source consumers are the legacy `CandidateValueObservation` methods above and feature-gated `shadow_scc` observations; `shadow_f5` also provides pending-application inventories. Tests in `src/tests/shadow_f5.rs` and `src/tests/shadow_scc_observer.rs` exercise exact identity/foreign-collection behavior. This is a separate owner from candidate graph export and must not be deleted merely because `CandidateInference` runs without a finalizer.

3. **Available successor owner — `CandidateInference` in `shadow_apply.rs`, with constructors in `candidate_source.rs` / `candidate_effect.rs` / `candidate_context.rs` and execution in `lib.rs`**
   - `CandidateInference::solve` preflights HIR/local-source owners; `ConstraintBatch::collect_candidate_mode_scoped` retains candidate source constraints; `InferenceSession::try_new_candidate(...).run_candidate()` propagates the graph. `export(root)` returns graph bounds; `fresh_use(occurrence)` returns candidate-graph substitution rows. Source-call inputs have separate retained `source_call(index)` observations.
   - This is the approved private successor path available for comparison, not a public/default inferencer. The root graph captures Value/Effect relations and has no closed F5 scheme finalizer. Its existence does not itself discharge the closed-output or source correspondence edges above.

4. **Initialization closed-scheme owner — `crates/yu-solver/src/shadow_initialization.rs`**
   - `ConstraintBatch::shadow_initialization_candidates` retains exact collection-branded candidates for original whole-Name self-initializer HIR shapes. `SolvedModule::shadow_initialization` joins only the same collection artifact and rejects another collection even when it was collected from the identical HIR. `SolvedInitializationRef::current_scheme` then checks the candidate's inventory brand and resolves its exact root through `shadow_closed_schemes().for_root`, returning a legacy `ClosedSchemeRef`.
   - `crates/yu-solver/tests/shadow_initialization.rs` clients consume that scheme for the exact `my f = f` source (including Bottom predicate check) and for a multi-definition unresolved boundary. The foreign-collection tests reject both a different solve's inventory at join time and a foreign candidate passed to `current_scheme`; separate same-spelling source artifacts also fail their source-position joins. These tests preserve identity/failure behavior; they do not grant initialization permission or establish source execution semantics.
   - This is an additional actual closed-output owner outside the earlier candidate source-crosswalk cone. The successor graph API does not return the `ClosedSchemeRef` this observer promises, nor does its graph export carry this observer's collection-brand contract.

5. **Historical-only accepted source carrier — `crates/yu-solver/tests/simple_sub_local_source_retirement.rs:67–68`**
   - On the fixture-only nested local binding `my apply f = { my step x = f x; step }`, `CandidateValueObservation::solve(historical.clone())` succeeds while `CandidateInference::solve(historical)` returns `CandidateError::Unsupported`. The next assertions distinguish it from the source-owned lowering: ordinary `CandidateInference` succeeds on the LocalSource carrier and retains function/effect flow.
   - Exact contract: this is a historical observer's fixture-only `ShadowLocalBind` carrier, not an approved production source domain. The observation confirms the old route and successor currently have different accepted HIR carrier sets; it does not authorize restoring that carrier, broadening source acceptance, or treating the fixture as a natural inference rule.
   - It strengthens the no-substitution result: replacing all historical observer calls with `CandidateInference` changes this concrete caller outcome today. It does not by itself preserve or validate the legacy route; the route remains historical and its eventual retirement needs an authorized consumer migration/removal decision.

## Source/native edges and exact missing correspondence

- Source declaration / expression -> retained HIR root and occurrence -> HIR-owned `LocalSource` / `CandidateSourceCall` inputs -> candidate source constraint recipes (`candidate_source.rs`) -> candidate Value/Effect rows and bounds (`candidate_effect.rs`, `candidate_context.rs`) -> propagation / graph export (`lib.rs`, `CandidateInference::export`). Existing native tests exercise these stages on candidate fixtures.
- Historical path is different: retained HIR preflight -> `collect_mode(..., true)` -> legacy `SolvedModule` execution and F5 finalization -> `ClosedSchemes::for_root` -> `CandidateExport` and closed use observers -> test crosswalk joins source `ShadowArtifact` positions / pending source Call stubs to `CandidateCall`, Name-use and root export.
- The crosswalk checks exact parse/HIR/candidate identity, occurrence/callee/argument incidence and source positions. It explicitly does not supply source typing, Call invocation meaning, effect hygiene, public export transport, or Q/R-to-source/successor identity. A structural join is not a semantic correspondence.
- Missing edge for migration: a proof/source-owned relation carrying the same original source assignment, source binders/roles, substitutions, Call/provider/effect obligations and later admissible lower/upper information from successor graph output to the old closed four-port endpoint and use-time scheme contracts. The open Catch-image / negative-port proposal is unapproved and cannot be used to fill this edge. Recursive/general sources, foreign continuations, annotation hygiene, complete Call, principality, and every current/later lawful bound remain in scope.

## Falsifiers and focused existing evidence (not executed)

A claimed smaller replacement boundary is falsified by any accepted historical caller or source shape for which the successor cannot preserve the exact observation contract: (a) `shadow_apply_candidate.rs` supported/rejected retained-HIR cases and closed endpoint checks; (b) `shadow_candidate_source_crosswalk.rs` once/twice Apply source-position and root export joins; (c) `shadow_candidate_multiroot_source_crosswalk.rs` independent roots and root-specific export identity; (d) `shadow_candidate_call_formation_crosswalk.rs` Call occurrence/callee/argument, raw pending suffix and exact provenance matching; (e) `src/tests/shadow_f5.rs` and `src/tests/shadow_scc_observer.rs` finalized scheme identity, foreign collection/root rejection and missing-identity cases; (f) `tests/shadow_initialization.rs` exact self initializer current scheme owner/endpoints, foreign collection rejection at both join and `current_scheme`, and separate same-spelling HIR/source identities; (g) `tests/simple_sub_local_source_retirement.rs:67–68` the fixture-only historical-accept/successor-reject split. Successor regression owners `ordinary_source_carrier.rs`, `ordinary_expression_source.rs`, `candidate_operation_catch.rs` and the rest of `simple_sub_local_source_retirement.rs` are corresponding input/constructor boundaries. These are source evidence locators, not proof of an old/new observational equivalence.

No test, build, probe, benchmark or runtime comparison was run, as forbidden by the packet. No existing test result is promoted to correspondence proof.

## Prior evidence reused / rejected

- Reused as bounded owner history: `notes/progress/2026-10-10-candidate-closed-lifecycle-retirement-next-gate.md` records the deliberate split: `CandidateInference` owns a `CandidateSolvedResult` without candidate finalization, while public `SolvedModule` and historical `CandidateValueObservation` remain legacy closed-result owners.
- Reused: `notes/progress/2026-10-10-simple-sub-legacy-withdrawal.md` says actual historical crosswalk clients and F5 closed schemes require a separate coherent migration; a parallel successor is insufficient. Rev2-pinned SHA-256: `150ce75b7d990017fdefb79998b68f0a74e8ba270ac4aff045deab423d0fdeed`. This remains bounded migration history, not current production authority.
- Reused as adversarial owner-path evidence: `notes/progress/2026-10-13-candidate-fallback-withdrawal-owner-audit.md` distinguishes `CandidateValueObservation::solve` from `CandidateInference`, and records actual `ConstraintBatch::collect` / pending-application F5 observers. Its older baseline-specific line inventory was not treated as current source truth.
- Reused: `notes/progress/2026-10-11-call-catch-export-source-audit.md` records the closed scheme ownership and unresolved Call/source/public obligations. Historical findings were checked against the current pinned source; no proof claim is imported.
- Rejected as cutover support: old fixture crosswalk green results, closed-scheme identity equality, graph capture, source-position identity, and CandidateInference's existence. None proves endpoint/profile/source assignment correspondence, ordinary accumulation equivalence, complete Call, or safe API substitution.

## Exact handoff to Luna: owner-specific NO_SAFE_CODE_SLICE

- `shadow_apply::CandidateValueObservation` / its `CandidateSourceCrosswalk` callers: no existing approved successor API is contract-compatible. Missing owner TODO: identify and prove the successor replacement for `CandidateExport`, exact target/receiving use schemes and fresh capture, and source Call/module-use/root join, preserving original guards and all current/later bound obligations. Falsifier: any supported crosswalk fixture changes or loses one of those observations or exact source identities.
- `shadow_f5::ClosedSchemes` and `shadow_scc::SccTopology`: no graph successor consumer has an approved Q/R-to-successor/source endpoint mapping. Missing owner TODO: establish the typed four-port/current-local scheme correspondence and exact use-time relation before removing these real F5 owners. Falsifier: foreign/recollected roots, SCC-internal or external uses, missing identity, or an endpoint/profile mismatch cannot be represented with the existing successor API.
- `shadow_initialization::SolvedInitializationRef::current_scheme`: the exact self-initializer observer also requires a collection-branded current `ClosedSchemeRef`, with foreign collection/candidate rejection. No successor scheme API currently implements that contract. Missing owner TODO: map this exact current scheme observation to the successor's source/root identity while preserving collection rejection and source positions, or retain it under the historical owner until an approved migration. Falsifier: a same-HIR re-collection or foreign candidate can join, the scheme owner/endpoints change, or the successor cannot represent the observed current root. This owner further supports NO_SAFE_CODE_SLICE; it does not make the initialization proposal or any production change authorized.
- `simple_sub_local_source_retirement.rs:67–68`: current evidence directly rejects a blanket switch of this historical fixture caller to `CandidateInference`, which is Unsupported for the same fixture. The fixture-only carrier is withdrawn from successor authority, so this is not permission to reinstate it. Missing owner TODO: define an authorized retirement or coherent migration of this historical client together with its owners; do not broaden LocalSource or pretend the two results are equivalent. Falsifier: any attempted blanket replacement loses this accepted historical observation or changes the source domain/semantics without approval. This strengthens NO_SAFE_CODE_SLICE rather than creating a new slice.
- `CandidateInference` / source constructors: successor graph and source-call evidence exist, but they do not close either missing output edge. Missing owner TODO: apply the original Call/effect parent to source -> constraints -> propagation -> graph export and establish the scheme/use correspondence without narrowing the source domain or adopting candidate semantics. Falsifier: authentic once/twice providers, annotations, recursive/general cases, foreign continuation, or later lawful lower/upper evidence fails to map.

No code lease is proposed from this inventory. If Luna later grants an exact implementation lease after the correspondence owner supplies its discriminator, the lowest-risk first code slice is a separately reviewed migration of a single source-crosswalk consumer with its exact falsifier set; current evidence does not establish that slice as ready.

## Dependencies and source hashes

Contract pins checked against the current source and matched:

- `crates/yu-solver/src/candidate_effect.rs` `44ee33d077c61c9dea6359299ca49218afc6ca1b5b6807690838309b25c731c9`
- `crates/yu-solver/src/candidate_source.rs` `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38`
- `crates/yu-solver/src/candidate_context.rs` `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6`
- `crates/yu-solver/src/lib.rs` `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`
- `crates/yu-solver/src/shadow_apply.rs` `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`
- `crates/yu-solver/src/shadow_candidate_source_crosswalk.rs` `392d665579a74810134846e1274c0c9ce975a7eb0e2cfb9ad79a07af2cd2eeb0`
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md` `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- `notes/design/2026-10-16-goal-driven-sprints.md` `2dfeb555c913d3142078de535ee4b7f68e9a27f2b91a5f0bb82d4d867db4fc4e`
- `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`
- `notes/design/2026-10-10-simple-sub-legacy-withdrawal.md` `93c2bf1c425522fdb41d0f4120d8430597a6091014741a64546e9fedb7bcf79a`

Additional inspected file hashes:

- `crates/yu-solver/src/shadow_f5.rs` `b6a6c70da75329ff66cd9e6c0a2598a54cc8f0de7ba956f6f28b24616ca3a994`
- `crates/yu-solver/src/shadow_scc.rs` `79e8ff5f459b6fc1389ecacb1da594814f9d9235297d62bc0501c2b3795b39c9`
- `crates/yu-solver/tests/shadow_candidate_source_crosswalk.rs` `5269e52d498df893e6c922cfa7c50a04a3907e05518a0766684ac91c2d3a1d82`
- `crates/yu-solver/tests/shadow_candidate_multiroot_source_crosswalk.rs` `eb0c86fa1cc10015c43465de6c1cf661264da9b0808eb467ced9611ff09cfb2c`
- `crates/yu-solver/tests/shadow_candidate_call_formation_crosswalk.rs` `08ecb92d2aebc15a4ae2102b977d24acc34889cea59d1fb6ed16cd7c3c82af7d`
- `crates/yu-solver/tests/shadow_apply_candidate.rs` `93506b15b5b0371570255a89642dca04d6fc7c54f0a78b4ab9ba4e77d5499b0c`
- `crates/yu-solver/src/tests/shadow_f5.rs` `1bcb1006b14c30fe4c79f5d4ee81ebce5a5fd8d47154b10868458ad30fbc534a`
- `crates/yu-solver/src/tests/shadow_scc_observer.rs` `ba84ff9edfd38aac6e7392159746523750cf7e9ce0c9e9be8a0ee89cef5f4c8d`
- `notes/progress/2026-10-10-candidate-closed-lifecycle-retirement-next-gate.md` `4b0e38b5d8975309a249de9869d4436a5da900a338b7ba5f8d4a9f0b205e7e16`
- `notes/progress/2026-10-13-candidate-fallback-withdrawal-owner-audit.md` `d57651250ce30e32860dc5291d14593c8579223724c233a7657043536a316843`
- `notes/progress/2026-10-11-call-catch-export-source-audit.md` `cd7cf21999e79a6cb448bbdc93d6ded8105abbce28bb75d34bdd22b18385b0f5`
- `notes/progress/2026-10-10-simple-sub-legacy-withdrawal.md` `150ce75b7d990017fdefb79998b68f0a74e8ba270ac4aff045deab423d0fdeed`
- `crates/yu-solver/src/shadow_initialization.rs` `6ea0914a11a4a05d6dde8d63c413cfd42fb887596b3315d998848d502a91715a`
- `crates/yu-solver/tests/shadow_initialization.rs` `5cd9fa3e7e63b24430a36c421f3aa0d7441c9926d953a16e4880bcbe48f579a0`
- `crates/yu-solver/tests/simple_sub_local_source_retirement.rs` `2349dcd2098ecaaa43ac3a19c8172a97dcab68a20853ae22cd3da75efa8b3a5e`

## Resources, stop and handoff freeze

Rev2 delta resources: one bounded source-read/edit stage; no tests/builds/probes. Cumulative exact active seconds and shell-reader CPU/memory are unavailable. Rev1 recorded its active estimate within 360 seconds; this short delta stayed within the same assignment envelope as far as observable runtime permits, but exact cumulative seconds cannot be authenticated. No budget transfer. Worker writes stop after this revision. There are no generated/scratch paths. No review is authored here; rev1 review is invalid for changed bytes and Luna's fresh delta review is pending.

Outcome class: source-native-evidence / owner inventory; parent application: exact owner-specific blockers and next evidence TODOs supplied to Luna; theorem, semantic, implementation, and production gates remain OPEN.
Next related step inside the existing envelope: none for this read-only assignment. Luna owns any later lease or authority change. The nearest related step is to assign the missing graph-to-closed-scheme/source correspondence and disposition of historical-only accepted observer clients to their actual proof/source owners; this handoff grants no such lease.

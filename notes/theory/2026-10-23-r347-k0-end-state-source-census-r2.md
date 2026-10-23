# R347 primary source census — K0 end-state adequacy

Status: **frozen primary census for R347 revision 2**. This is an owner map, not a proof of projected solution equality, a test result, or a compiler defect.

Revision 2 preserves the immutable revision-1 census at `notes/theory/2026-10-23-r347-k0-end-state-source-census.md`, SHA-256 `f42cdefcb9d0a59d8111be84e33403bec5f9ea6b5bbb5348caf10b2181bfd220`. It adds the four direct recipe/admission owners required by the source trace and records the corrected `candidate_context.rs` pin in current state. No source file changed.

## Authority and pinned baseline

- Branch/upstream: `research/simple-sub-intrusion` / `origin/research/simple-sub-intrusion`.
- Baseline at admission: `726edb1a3f81bc525ed93b7913dc300e268cd109` (HEAD matched upstream).
- Original audit SHA-256: `b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`.
- Latest whole-language semantics SHA-256: `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65`.
- R341 accepted retention proof/outcome SHA-256: `f8607d11c417734c1a7fb5aafe1af7ca78a587c5f5e7189c8cf3dcbc2064343f` / `7e5a5905a49335cf7c314da6fd33e800a9552109b638ee5914b050f2b20602bc`.
- R346 accepted proof/outcome SHA-256: `f21a15eac621216366338ceeb454aec868554668a6cc4b8da903aa79d9d2fc7d` / `25748200d206c375a2e450aff688f692a4bfc5537ef7ba3fdc953423006b6512`.

The six R341/R346 solver-source hashes match the admitted R347 contract; revision 2 adds four direct recipe/admission owners:

| Owner | SHA-256 |
| --- | --- |
| `candidate_source.rs` | `0dc798e48e70505093e52b31b2569e3b2d8ff1dee663095176aaf547ccb3289b` |
| `lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `candidate_context.rs` | `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5` |
| `candidate_effect.rs` | `d156fdbf0300387a5aa036053a2cc7eeb6312a803aaf38838e30dd2731ca4945` |
| `candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` |

## Fixed claim boundary

R341's `H(S)` is written `H₀(S)` here only to avoid colliding with the newest TeX's packet field `H` (evidence holes/DAG) and language name `Y_H`. It remains the exact independent conjunction defined in R341 §2: directed physical bounds plus its live-work/frame formulas. `C_s` is R341's authentic K0 source inequality family, retaining occurrence identity for the source inventory. R347 asks for projected solution equality under an explicit kind-preserving map; this census does not establish the new lifting direction.

The R341 theorem supplies only `H₀(S) ⇒ C_s` for the reviewed K0 completion premises. R346 supplies the exact ordinary fixed-key replay delta and actual owner chain for its family. The current census gap remains how every authentic source origin—including source-side suppression before a bound receives `OwnerEmission`—is represented in the actual final state or entailed by its physical bounds, and whether every source solution extends to all final native coordinates.

## Source schedule and source owners

`InferenceSession::execute` runs `execute_scc_plan`, then for candidate source mode runs loose source actions and scheduled expressions (`lib.rs:10637–10664`). Operator-provider roots can be skipped only when their separate operator graph owns them (`10648–10658`); operators are outside the contracted K0 source domain. The source driver advances `CandidateSourceState` actions in order and clears the source frame only after its action list ends with empty local-capture stack and zero source-Lambda depth (`candidate_source.rs:2390–2413`).

The seven K0 constructor families and Definition-root `Action::Link` are inventoried in the accepted R341 census, including their source occurrence, Value/Effect endpoints, and emitted inequalities. The action consumer dispatch is at `candidate_source.rs:2415–2464`: `Fact`, `Link`, `ValueConstraint`, candidate recipe and Lambda recipe reach typed admission; local/module/role/primitive and other arms are outside this K0 contract unless a source-path audit finds an authentic K0 route. The census must preserve each occurrence and distinguish a source fact from its later memo key or replay child.

Open source-side owner checks for this sprint:

1. Complete the exhaustive K0 occurrence-to-action inventory using the seven constructor families and root Link already accepted in R341; this revision traces the direct recipe/admission owners and finds no pre-admission cache in those inspected paths.
2. If another authentic origin has a suppression point, identify its exact earlier admitted source occurrence/owner and prove the source formula is already entailed. Memo identity, duplicate `FactId`, or a completed-generation stamp is not that proof.
3. Complete the end-to-end per-family endpoint/polarity map through actual Value/Effect work and successful completion, including every auxiliary fresh coordinate. The present trace is not the lifting proof.

At `lib.rs:11481–11527`, successful `admit_collected_fact` receipts record provenance, derive kind-correct polarized endpoints, and call the live constraint path. The R341 proof separately checks successful fresh and duplicate receipts as logical `H_after = H_before ∪ {q}`; store equality alone never proves prior entailment. Source `Action::Link` and `Action::ValueConstraint` call their candidate Value-link admission at `candidate_source.rs:2427–2437`; revision 2 pins the reached typed owner in `candidate_scheme.rs:4778–4789`.

### Revision-2 direct recipe, term and admission trace

The actual run schedule is part of the identity argument. `run_candidate` calls `execute` exactly once, then field-tail processing and `finish_candidate` (`lib.rs:10631–10690`). `execute` enters `execute_scc_plan` before source-mode loose/expression schedules (`10637–10664`). The candidate SCC plan visits each component in dependency-first order and executes each definition root schedule once before graph capture (`candidate_scheme.rs:2829–2864`). The post-SCC phase runs the loose schedule once and each expression schedule once, with only an operator-provider-root skip guarded by a published operator graph (`lib.rs:10646–10658`); that skip is outside the contracted K0 domain. The source driver advances an action index only after the action returns successfully. Thus an occurrence spelling alone is not used to justify repeated entry/return auxiliary rows: the contracted actual schedule supplies one source execution per root/action.

The collector appends `ConstraintOccurrence`s in `lib.rs:2146–2160`; this operation increments source counters and contains no source-side pair-cache branch. The source helper `candidate_source.rs:560–564` appends each action to its `Vec`. Each K0 candidate recipe is appended by `shadow_apply.rs:3685–3720`; the source action is then scheduled as `Action::Candidate` by the collector, including Apply at `candidate_source.rs:1826–1880`. `step_candidate_source` reads the exact next action and advances its cursor only after `execute_candidate_action` returns successfully (`candidate_source.rs:2378–2413`). These direct construction/schedule owners show no source-side cache suppression before the admission call; a failed or incomplete action is not a successful completed state.

`Action::Link` and `Action::ValueConstraint` derive the lower endpoint and call `candidate_scheme.rs:4778–4789`, which builds `ConstraintOccurrenceId` and `CauseId`, records provenance through the pinned `lib.rs` store owner, then invokes live Value constraint handling. `Action::Candidate` reaches `shadow_apply.rs:3942–4265`. Its `CandidateRelation` constructors cover Group, Apply, Record, Tuple, Variant, VariantCase and TuplePattern. Admission creates each structural term with explicit polarity and source row endpoints, builds the `ConstraintOccurrence`, records provenance, and only then consults `constrain_live_value`. For effect-enabled Apply, it allocates one invocation-effect row and admits the callee/invocation effect occurrences; tuple/record/variant element effects are admitted in their source slots. Missing case-pattern payloads allocate additional level-indexed Value coordinates. Their allocation is in the already pinned `lib.rs:10456–10500`.

`term.rs` owns `Term`, `TermView`, the typed `TermNode` constructors and the term arena's structural interning. That may share an equal term node; it does not deduplicate the separate source `ConstraintOccurrence`. `candidate_call.rs` is an admission dependency because `shadow_apply.rs:3946–3965` validates every retained Apply source input against the registered recipe, including its endpoints via `same_endpoint`. The subsequent `NativeInterface`/`DirectionalIntroduction` write is sidecar metadata, not an `H₀(S)` constraint; scoped-Apply authentication remains outside the contracted K0 domain because it is guarded by `scoped_experiment`.

The typed Value/Effect pair cache is downstream of `admit_and_record_provenance`, so it can suppress repeated work but not erase the source occurrence. The exact duplicate receipt and its logical contribution are covered only by R341's stated premises. No cache bit, memo identity or completion stamp is used as an entailment argument. The new proof must still account for every allocated auxiliary coordinate in its kind-preserving extension/projection; this census does not prove that lifting.

## Propagation, physical owners and work completion

`constrain_live` enters the typed work machinery at `lib.rs:13947–14003`; candidate mode starts a retained drain and enqueues the incoming item before dispatch (`14186–14231`). Each popped item is placed in `frame.current` before transport/dispatch and exact replay acknowledgements are moved to frame ownership (`14047–14103`). The queue-empty branch checks dirty intrusion and retries before ordinary drain completion (`14066–14069`). The census must link each generated bound formula to its source antecedent, source occurrence and final owner, including R339/R345/R346 families only under their exact premises.

Physical bound insertion/interpretation is owned by `candidate_extrusion.rs:619–875` and `candidate_context.rs:3305–3325`. `bound_pair` reconstructs the directed typed pair from owner, polarity and item. `candidate_effect.rs` distinguishes `OwnerEmission`, `BoundTransport`, cache and completion facts; only the actual exact owner-side bound or independently justified surviving formula contributes to the source correspondence. `candidate_intrusion.rs:380–596` owns pending-parent settlement; `merge_candidate_rows` changes representatives, canonicalizes bounds, increments generation and reopens work (`599–705`). R336 L0 is a premise restricting such producers in K0, but the R347 census must verify the precise authentic call path rather than infer absence from the file-level existence of merge code.

The source completion owner is `run_candidate` (`lib.rs:10672–10678`): execute source/SCC schedules, process field tails, then enter `finish_candidate`. The latter rejects unresolved active field-tail selections before calling `finish_observations` (`10680–10691`). For this packet, the candidate-state S is the actual state immediately at that successful observation boundary, with R341's `NativeComplete₀` checked independently; success of `run_candidate` alone is not its definition. `finish_observations` projects a limited `SolvedProjection` from physical direct bounds (`19807–19879`) and consumes the session. That output projection is not assumed equal to `H₀(S)` or `C_s`; proving such an output equivalence is outside this packet.

## Current evidence levels and unresolved seam

| Evidence level | Established input | R347 question |
| --- | --- | --- |
| Source enumeration | R341's seven constructors and root Link; source action schedule owners above | Are all authentic K0 source occurrences emitted or soundly suppressed before owner admission? |
| Operational ownership | R338–R346 bounded drain, retirement, and replay results | Do all actual K0 generated/suppressed formulas reach a final bound, live owner, or exact surviving entailment? |
| Algebraic interpretation | R336 finite Value/Function and Effect algebras; R341 `H₀(S)` | Does each native formula follow from `C_s`, with an explicit projection/lift for auxiliary rows? |
| Compiler behavior | No code change and no defect established | Does not establish current whole-language compiler correspondence or A/B closure. |

The remaining gate is the right-to-left projected solution lifting from `C_s` to actual `H₀(S)`, plus a source-complete suppression/origin inventory. If the attempt stops short, record the first exact missing origin, transition, map coordinate or premise. Do not infer a counterexample from an uninhabited assignment or from an unreachable native state. No tests, builds, Cargo, or execution probes were run for this census.

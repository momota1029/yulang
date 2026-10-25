# Sprint FORCE-LOCAL-APPLICABILITY-20261025 — source Force result transport

Status: FROZEN ACTIVE CONTRACT
Branch / baseline: `research/simple-sub-intrusion` / `b93cca3ba56eaf633c9228c16142aac55ed18b17`
Authority: accepted typed-value transport direction and pinned Force/transport clauses below; `rules/goal-driven-sprints.md` §§1–7
Revision / primary: r12 / Luna

## Unchanged goal and exact question

Original user goal remains complete proofs of Yulang semantics and type inference in `notes/theory/lean`, on the original accepted source domain and quantifiers. N1, O-NORM, O-RESULT, source/native correspondence and the parent remain OPEN.

Resolve the exact r10 question `accepted_force_leave_entails_result_transport` at the source/authority boundary. For each retained refined typed Force/Delay derivation, one consistent packet/type/owner interpretation, an actual finite normal return with operand `t : U(E,A)` and returned body packet `r : A`, and each finite typed suffix `p` of the result instance, determine whether the applicable accepted clauses entail the source-selected normal-leave relation. The discriminator must preserve the operand suffix `force.result · force.effect` separately from `force.effect` on a returned thunk.

Required adjudicable result, without narrowing the source domain:

1. derive from accepted clauses a complete normal-leave constructor/equation binding actual operand, actual returned packet, fresh or otherwise authorized output occurrence, exhaustive incoming typed correspondences, all relevant domains/images and allocation; then derive the all-finite-suffix result-route relation and apply the r11 abstract completion lemma only after its actual source premises are established; or
2. give a source-qualified counterexample, or two complete clause models disagreeing on the returned-thunk discriminator, that satisfies every relevant accepted clause, common typing/profile/latent-path/owner/alias/allocation condition, and explicitly identifies the violated universal claim; or
3. report the exact missing source clause/decision and why neither derivation nor complete model separation follows from the pinned inputs.

A conditional derivation from `LOCAL-LEAVE`, Draft §6, an assumed transition checker, a partial model, or a candidate row batch is not outcome 1 or 2. Do not claim semantic underdetermination unless all relevant accepted clauses and their shared interpretation are covered. Do not adopt a new semantic rule; any adoption or implementation decision returns to the existing authority process.

## Two lanes and method

**Proof/source lane:** one bounded `astra_prover` assignment first, maximum 300 seconds, medium effort, at most three substantive stages: invert the accepted source clauses; attempt a complete route/provenance derivation for the actual Force normal leave; attack the universal claim with a complete model-separation construction on the returned-thunk discriminator. After confirmed STOP and Luna handoff, one Sol/high `prover` may continue the same unchanged claim for at most 1,200 seconds, refining the construction, deriving all finite suffixes or completing the falsifier. Both authors share one exclusive output and one assignment handoff; the second writer starts only after the first is confirmed stopped and Luna acknowledges sequential transfer. Neither author reviews the combined result.

**Implementation lane:** Luna/high continues r10 `NO_SAFE_CODE_SLICE`. Existing inspection covers the annotation/decorator/export seam and Delay/normal-Force completion (`candidate_scheme.rs`, `machine.rs`, `receiving.rs`); current evidence shows no independently approved constructor/exporter or safe production edit. No compiler write lease is issued. If the proof reveals a source-grounded exact equation, a later separately versioned contract can allocate Lean representation or an approved implementation slice.

The mathematical method is inversion of the exact accepted clauses followed by a graph-cut/relational-image derivation; for refutation, model construction must satisfy the entire relevant clause set. The discriminator is a returned thunk with nested `force.effect` and `force.result.force.effect`. A witness that loses either suffix, changes identity/owner/profile premises, omits aliases/allocation, assumes LOCAL-LEAVE, or invents a transition is a falsifier of the proposed evidence, not a counterexample to Yulang.

## Frozen authority and evidence pins

- Baseline: `b93cca3ba56eaf633c9228c16142aac55ed18b17`.
- Source manuscript `docs/yulang-source-type-safety-ja.tex`, SHA-256 `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`; inspect the actual Force, normal return, path, identity and finite relation clauses, especially the cited regions in r10 R.
- Typed-boundary realization draft `notes/design/2026-10-02-typed-boundary-realization-draft.md`, SHA-256 `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb`. Its §6 is a candidate only.
- Redesign charter `notes/design/2026-09-29-scc-intrusion-redesign-charter.md`, SHA-256 `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed`; typed-value transport direction applies, while §6 representation/applicability remains unadopted.
- Hygiene integration `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`, SHA-256 `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`; reuse only under its supplied typed-correspondence premises.
- Top-level inference principles `notes/design/2026-10-11-yulang-inference-top-level-principles.md`, SHA-256 `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- r10 R conditional route-cut handoff `tasks/agent-loop/inbox/20261025-force-return-entailment.md`, SHA-256 `414b6c301d66bf1d331c8b4d4944f230ec1e886b1f5d4fcc74e046d61b99c12f`; r10 outcome SHA-256 `5f445c4e693387496a3d9a232c9ed9f273509dd6c1f71aa6e6de8e890f80c62d`.
- r9 runtime obstruction `tasks/agent-loop/inbox/20261025-force-runtime-return-trace.md`, SHA-256 `208834c17ad78d4994cf9596bc9f6e9fd275691e9f60d2d10c7baaa9d2b321c4`, evidence only, not semantic premise.
- r11 accepted abstract theorem `notes/theory/lean/YulangClosure/ForceCompletion.lean`, SHA-256 `6baeb9a786e916d0f7b60bd4d5c8286657da2adba4acdab36f2e45e0921aeb22`; use only after source premises are derived.

Revalidate direct hashes before each author stage and before review. Any changed authority or new semantic decision suspends affected work and returns to Luna.

## Exact leases, capacity and verification

- Shared exclusive author outputs: `notes/theory/2026-10-25-force-local-applicability.md` and `tasks/agent-loop/inbox/20261025-force-local-applicability.md`. Astra owns first; Sol may write only after STOP plus explicit Luna transfer. No wildcard, scratch or other output paths.
- Reviewer: one fresh nonauthor `compiler_referee`, read-only, 600 seconds, after both authors STOP. Independently audit clause completeness, source qualification, model coverage, suffixes, allocation, aliases, output identities, counterexample validity and the route-cut derivation. No author/coauthor may review.
- Conditional Lean slot: 120 seconds, one CPU, 1 GiB, serialized, only if the source derivation first yields an accepted, fully encoded proposition and Luna validates the input entry. No Lean file write or checker execution is authorized by this contract absent that entry; otherwise the slot expires unused.
- Fresh cap 2,700 seconds: Astra 300 + sequential Sol 1,200 + independent review 600 + conditional Lean check 120 + Luna integration 480. No carryover. One active author at a time, max six active/reserved/unknown assignments including three quarantined UNKNOWN reservations, Luna and the review reservation. Zero compiler/test/build/runtime processes; no tests.
- STOP on contract/dependency change, user STOP, true semantic-choice boundary, exhausted stage/time, or inability to make progress without changing the claim. No automatic renewal or inference of cessation from elapsed time.

## Closure, integration and next trigger

The r12 packet succeeds only by one of the three adjudicable outcomes above, with before/after parent evidence and a fresh review. If outcome 1 is established, identify exactly how it consumes the r11 lemma and which N1/O-NORM/O-RESULT premise becomes smaller. If outcome 2 is established, retain the original claim as refuted and block only dependent production. Outcome 3 leaves the source theorem OPEN with an exact owner/decision; it is not a proof or countermodel.

Keep N1, O-NORM, O-RESULT, source/native correspondence and the original parent OPEN until their original obligations are discharged. Only Luna adjudicates the source meaning, synchronizes current/outcome records, stages explicit paths, inspects the complete outbound range, and commits/pushes non-forced.

Next dispatcher consultation: frozen proof/model/obstruction result, source-authority or dependency change, material counterexample, or resource boundary—not internal lemmas or commits.

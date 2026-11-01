# Sprint R178 — App demand to original Checking

Contract revision: 3. Prior rev2 SHA-256: `255bf8ed15a0a87c9171ac8f54a06e74e9930741b66e2b87be4678966b9c04f8`. Rev2 source/proof lanes stopped at newly identified unpinned owners; no unpinned content was read.

Status: ADMITTED for the unchanged Yulang type and inferred-effect soundness
goal. Baseline: `yulang3` at `8fbcfcd6d`. Luna owns integration and Git.
Rust-program/runtime correctness is excluded.

## Parent and fixed outcome

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness`
(`Contracts.lean:127–130`), with its original source domain and quantifiers
and one shared `sameScoped` witness for the same solution. R177's reviewed
result fixes the actual CandidateInference Apply operands and original App
goal, but does not construct the original admitted ViewLogic or finite
Checking premises.

Construct from the actual candidate Apply demand and Function comparison the
original App value-check target:

```text
exact source-owned Apply/callee/argument and candidate Function comparison
  ⊢ ∃ v, original.admitted ρ ⟨site,.viewLogic,0⟩ v ∧
       Checking original (ρ.extend ⟨site,.viewLogic,0⟩ v)
         ⟨.value,site,Γ,⟨callee.site,.returnedValue⟩,⟨site,.descriptor⟩⟩
```

Use genuine source-induction and recursive comparison hypotheses only where
the original rules justify them. Construct the original admission, descriptor,
and finite Checking derivation from existing source rules and actual solver
operations. Function checking must retain its same-callable checked-domain and
whole-tuple observation obligations; endpoint equality or four-port shape
alone does not discharge them. Apply the result to R177's exact App value goal.

Deliver an actual original admitted-value/`Checking` construction, or a
source-qualified failure with exact operands. If the required source or solver
invariant is absent, stop with its exact owner and keep R178 **BLOCKED**; do not
add an opaque acceptance-to-Checking premise, false-kernel countermodel,
guard-only theorem, or assumed original `Build`. Computation checking, the
remaining App atoms, complete Call, complete Build, and the parent's shared
same-solution `sameScoped` witness remain explicit downstream obligations.

## Frozen baseline and direct inputs

Rev2 strictly parsed and verified all 32 direct path entries. Newly identified owner paths are admitted only by a sequential revision; every listed SHA-256 must match before new content is read. If a named
comparison/context/representation owner is not pinned, stop and return its
exact path for a sequential primary revision.

- `crates/yu-solver/src/shadow_apply.rs` —
  `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5`
- `crates/yu-solver/src/lib.rs` —
  `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`
- `crates/yu-solver/src/candidate_context.rs` —
  `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`
- `crates/yu-solver/src/candidate_scope.rs` —
  `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03`
- `crates/yu-solver/src/f5c_generalization.rs` —
  `928607961bff9ab747fd759aed1dacd3aa13abc9e20bf3bb8a957a4c7bd12ffb`
- `crates/yu-solver/src/f5c_replay.rs` —
  `71fb166c38dbd93571abcbc3ff290b3b79fe2a4ecba8159edd5f60933c8b3b2a`
- `crates/yu-solver/src/term.rs` —
  `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`
- `crates/yu-solver/src/candidate_source.rs` —
  `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`
- `crates/yu-solver/src/candidate_call.rs` —
  `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`
- `crates/yu-solver/src/candidate_scheme.rs` —
  `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e`
- `crates/yu-types/src/lib.rs` —
  `fb3d53cdcce6a2d7149508ba0bdc9dad643cfc795fefdb9914afcb461e4aa6d8`
- `notes/theory/lean/YulangClosure/Contracts.lean` —
  `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` —
  `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`
- `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` —
  `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`
- `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` —
  `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
- `notes/theory/lean/YulangClosure/OriginalParameterSemantics.lean` —
  `733c5b05e0db226f95d14ff2161c46e9a389b43d86b365b000a9656ec4fd0bd2`
- `notes/theory/lean/YulangClosure/OriginalParameterWorld.lean` —
  `7b5f849f744dbe56f374d8be6b11a5a218176abf6eeda2fb9da8180c7b1ff802`
- `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` —
  `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `notes/theory/lean/YulangClosure/OriginalSourceChecking.lean` —
  `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`
- `notes/theory/lean/YulangClosure/OriginalCheckingAdmission.lean` —
  `77a8dd74f5913814d3628f0aed189be24b4aafc4780839eaa57237676a157da7`
- `notes/theory/lean/YulangClosure/OriginalFunctionFuture.lean` —
  `e90f98aa00597cf46089f2152b492ab98b21b0ab5350276410b622931439c99f`
- `notes/theory/lean/YulangClosure/OriginalCalleeDelayProvenance.lean` —
  `3acb041c530b19e78703b3f3030edd1b304ab7c20329974f0afc2d387428dbfe`
- `notes/theory/lean/YulangClosure/OriginalFormalAdmission.lean` —
  `77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c`
- `notes/theory/lean/YulangClosure/OriginalSourceOwnerReification.lean` —
  `95d9749ce93ecfc82d6423ba193a261f2725178a7e62cea469b57ae316af3d7e`
- `notes/theory/lean/YulangClosure/OriginalSourceEvents.lean` —
  `cfd5f502a1e68a97e27e11a75400fae8789f167c92596aedb08ef7dfbb724342`
- `docs/yulang-source-type-safety-ja.tex` —
  `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`
- `docs/yulang-semantics-and-soundness-ja.md` —
  `2a0b173406353524950e1ab690c679918185167e63929c9b6724547b5cd379f2`
- `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` —
  `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`
- `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` —
  `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md` —
  `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- `tasks/agent-loop/sprints/candidate-acceptance-construction-r177.md` —
  `e3279f46a5076e833d3407b0a64214888fe443bd95badbb1c83a37c444c6af31`
- `tasks/agent-loop/inbox/candidate-acceptance-construction-r177-source.md` —
  `36f0ff4757d2881fa7383b807df3a915990f1c213445075ebfd2d6633bf0a877`
- `tasks/agent-loop/inbox/candidate-acceptance-construction-r177-proof.md` —
  `b5ab4b8ac2deb186aec7eb7b87b0fde02967af59179e2706bb8b7d8414062154`
- `tasks/agent-loop/history/candidate-acceptance-construction-r177-activation.md` —
  `41123e34dbd556caa9580b0528ae6ba6c260eb4633210670feddd156022a8feb`
- `tasks/agent-loop/history/candidate-acceptance-construction-r177-pin-correction.md` —
  `b778191b8a4c2aa243d0c997d78fa8aaaad3d415e3c2e4f8133cb4e92d3ad5f6`
- `tasks/agent-loop/history/app-demand-original-checking-r178-rev2-correction.md` —
  `a2f14a6ba9fa11ccbf9666a6a601dd2e487a77cb6a0b637115de28e52be62afc`
- `tasks/agent-loop/history/candidate-acceptance-construction-r177-pin-correction-r2.md` —
  `5d3fdaeea129e8fb1d051f23b76db1b7c111a4fd52bf82e4cf239267107d9003`

The Rust owners are read-only. No Cargo, tests, build, runtime, cache or
environment creation, compiler edit, or access to pending/quarantined paths is
authorized.

## Lanes, leases, and verification

- Source lane: one registered researcher, 900 seconds, read-only. Trace the
  negative Function demand in `shadow_apply.rs`, Function-pair dispatch and
  child work/replay in `lib.rs`, and the exact `candidate_context` continuation
  state. Report the exact guard/capture code, contravariant checked-domain
  child, universally quantified same-callable observation child, visited-pair
  or cycle behavior, and the first missing semantic invariant. Sole output:
  `tasks/agent-loop/inbox/app-demand-original-checking-r178-source.md`.
- Proof lane: one registered `lean_prover`, 1200 seconds, sole owner of the
  existing pinned `.lake`. Construct original admitted ViewLogic and finite
  value Checking from genuine original/source-recursion premises and actual
  candidate operations, then apply to the exact R177 App value goal. Leases:
  `notes/theory/lean/YulangClosure/AppDemandOriginalCheckingR178.lean` and
  `tasks/agent-loop/inbox/app-demand-original-checking-r178-proof.md`.
- Fresh independent reviewer: 300 seconds after exact outputs and inputs
  freeze. Luna owns intake, exact hash validation, review assignment,
  adjudication, current-state reconciliation, staging, commit and push.
- At most one focused theorem check plus required import build, pinned Lean
  4.35.0, existing `.lake` only, 1 CPU, 1 GiB and 180 seconds total. No default
  build. If no theorem is constructed, run no Lean command.

Preserve all UNKNOWN worker rows and quarantined paths. Stop on missing source
authority, an unjustified function-cycle cut, unsupported original admission,
counterexample, dependency expansion, or resource limit. A local value-check
result does not close full Call, effects, `InferenceSoundness`, or production
readiness.

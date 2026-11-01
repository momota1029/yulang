# Sprint R177 — candidate acceptance construction (contract revision 3)

Status: ADMITTED for the unchanged Yulang type and inferred-effect soundness
goal. Baseline: `yulang3` at `ec88e8ff10aee4a2f29f19b6d04ac6800249e7bf`.
Luna owns integration and Git. Rust program/runtime correctness is excluded.

## Parent and fixed outcome

The original parent remains `YulangClosure.SourceProblem.InferenceSoundness`
(`Contracts.lean:127–130`), with its original source domain and quantifiers
and one shared `sameScoped` witness for the same solution. R176 closed
incomplete under independent review: ordinary `SolvedModule::solve` publishes
diagnostic observations, but the available evidence does not connect its `Ok`
to original source acceptance or complete generated-obligation discharge.

R177 follows the distinct `CandidateInference` consumer identified in R176.
Construct its operational result relation from the pinned preparation,
selected solve mode, same-HIR/conflict guards, and actual export prerequisites.
Preserve exact module/HIR identity and the returned candidate carrier. Connect
the resulting relation to one precise original Call typing/effect obligation
using the existing original source-generation and judgment definitions.

Deliver either a checked implication for those exact branches, with every
supplied premise named and its application to the selected original Call shown,
or a concrete failed implication with exact branches/operands. A guard-only
relation, `Ok`/export success by itself, a private/conditional semantic
registration, or a Rust execution claim does not satisfy the outcome. Do not
define parent `solves`, assume original `Build` satisfaction, narrow the
original source domain, or claim that the parent is closed. Complete source
clause discharge and construction of the same shared `sameScoped` witness
remain explicit downstream obligations.

## Frozen baseline and direct inputs

Every listed SHA-256 must match before new content is read. If another owner or
semantic authority is needed, stop and return its exact path for a sequential
primary contract revision.

Revision 1 SHA-256 was `2f2f9e60860b17ee33a6cb7a31bb639b3802ac2cefd371cd26562cc94048b303`.
Both lanes acknowledged and paused revision 1 before revision 2. Revision 2
SHA-256 was `5c8584e2887a9bf7fa5cb444b56ecb4c097ba98e1f5f6a62dcb99ae90cc31255`;
both lanes acknowledged and paused it before this sequential revision.

- `tools/inference-playground/src/lib.rs` —
  `45bf78af436efa50e02ca97ba3b639c11f7dd88272d87c47f2822643786653d4`
- `tools/inference-playground/Cargo.toml` —
  `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56`
- `crates/yu-solver/Cargo.toml` —
  `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`
- `crates/yu-solver/src/shadow_apply.rs` —
  `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5`
- `crates/yu-solver/src/candidate_call.rs` —
  `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`
- `crates/yu-solver/src/candidate_source.rs` —
  `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`
- `crates/yu-solver/src/lib.rs` —
  `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`
- `crates/yu-types/src/lib.rs` —
  `fb3d53cdcce6a2d7149508ba0bdc9dad643cfc795fefdb9914afcb461e4aa6d8`
- `tools/inference-playground/src/pinned_stdlib.rs` —
  `3d1a32946e764effd354271653e68edd1b2edaf980f51ea5178ad21adb633d4e`
- `tools/inference-playground/pinned_stdlib.bin` (opaque, hash only) —
  `9eb726f179fa407122f1c31f4cd4cf98484bce3052d2486d7d7be84d4ec22b66`
- `crates/yu-solver/src/candidate_scheme.rs` —
  `6072c73bc1a1629f025cfbeba147c55898fea5d27463c490db2875b05308fec`
- `notes/theory/lean/YulangClosure/Contracts.lean` —
  `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` —
  `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`
- `notes/theory/lean/YulangClosure/OriginalParameterSemantics.lean` —
  `733c5b05e0db226f95d14ff2161c46e9a389b43d86b365b000a9656ec4fd0bd2`
- `notes/theory/lean/YulangClosure/OriginalParameterWorld.lean` —
  `7b5f849f744dbe56f374d8be6b11a5a218176abf6eeda2fb9da8180c7b1ff802`
- `notes/theory/lean/YulangClosure/InferenceConstruction.lean` —
  `576d69266da62c0f75fa9748ff0f0691a9f0bc3aca5148be9d25cef82d2010f0`
- `notes/theory/lean/YulangClosure/OriginalProofProgress.lean` —
  `21e361962538d5e2738041b58186682a4a9fb3ad10c75f4c39dc97e32a443f39`
- `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` —
  `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` —
  `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
- `notes/theory/lean/YulangClosure/OriginalSourceChecking.lean` —
  `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`
- `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` —
  `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md` —
  `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- `docs/yulang-source-type-safety-ja.tex` —
  `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`
- `docs/yulang-semantics-and-soundness-ja.md` —
  `2a0b173406353524950e1ab690c679918185167e63929c9b6724547b5cd379f2`
- `docs/yulang-whole-proof-closure-ja.md` —
  `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`
- `notes/design/2026-10-08-source-generalize-definition.md` —
  `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`
- `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` —
  `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`
- `tasks/agent-loop/sprints/ordinary-solution-adequacy-r176.md` (R176 contract) —
  `7b10f0542ada0283f215cfbeba147c55898fea5d27463c490db2875b05308fec`
- `tasks/agent-loop/inbox/ordinary-solution-adequacy-r176-source.md` (R176 source handoff) —
  `1389c4d0c7d928c43b4405247a5aa46cfe6cd203a6589b372c8f077cf21a4618`
- `tasks/agent-loop/inbox/ordinary-solution-adequacy-r176-proof.md` (R176 proof handoff) —
  `9f1364353ac2c8518bbc2e469fae8553d0d293802ad96649cebb0cd4101f6c14`
- `tasks/agent-loop/history/ordinary-solution-adequacy-r176-activation.md` (R176 closure) —
  `aa6d9a93eb012213dd239008ea310319df203f65eff7c5d07f11a8544975c4de`

The first seven Rust authorities and the pinned Lean/source authorities are
read-only. No runtime subtree, pending question, quarantined path, Cargo,
tests, build, execution, cache/environment creation, or compiler edit is
authorized.

## Lanes, leases, and verification

- Source lane: one registered `researcher`, 900 seconds, read-only. Trace
  `prepare` → exact `CandidateInference` mode → same-HIR/conflict checks →
  export guard/result. Identify the exact Call/type/effect obligations covered
  and first missing semantic invariant. Sole lease:
  `tasks/agent-loop/inbox/candidate-acceptance-construction-r177-source.md`.
- Proof lane: one registered `lean_prover`, 1200 seconds, and sole owner of the
  existing pinned `.lake` cache. Construct the operational relation and exact
  branch implication, then apply it to one original Call obligation or return
  a concrete failed implication. Leases:
  `notes/theory/lean/YulangClosure/CandidateAcceptanceR177.lean` and
  `tasks/agent-loop/inbox/candidate-acceptance-construction-r177-proof.md`.
- Review: one fresh independent reviewer, 300 seconds, after both outputs and
  their exact inputs freeze. Luna owns intake, review assignment, adjudication,
  records, staging, commit and push.
- At most one focused theorem check plus its required import build, pinned Lean
  4.35.0, existing `.lake` only, 1 CPU, 1 GiB and 180 seconds total. No default
  build. If no theorem exists, do not run Lean merely to probe imports.

Preserve all UNKNOWN worker rows and quarantined paths. Stop on an unpinned
owner, unsupported semantic interpretation, reachable counterexample, missing
cached dependency, or exhausted resource envelope. A partial correspondence is
not parent closure or production authority.

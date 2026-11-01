# Sprint R176 — ordinary solution adequacy (contract revision 3)

Status: ADMITTED under the unchanged Yulang type/inferred-effect soundness
goal. Baseline: `yulang3` at `6a7e31c39`. Luna owns integration and Git.
Runtime/machine correctness is excluded.

## Parent and fixed outcome

The unchanged parent is
`YulangClosure.SourceProblem.InferenceSoundness` (`Contracts.lean:127–130`):
all original supported source forms and quantifiers remain in force, and the
conclusion uses one source derivation and one shared `sameScoped` witness for
the same solution. Parent remains OPEN.

R175 independently reviewed `BLOCKED_SOLUTION_REGISTRATION`: source typing
and effect laws are already defined, but the actual solver solution/success
relation is not registered to original Descriptor/Interface meanings. Do not
repeat that absence audit. Investigate the ordinary public inference path's
actual acceptance decision and its generated obligations.

Fixed outcome: trace source collection → generated type/effect obligations →
processing and error retention → finalization/publication → the ordinary API's
actual acceptance decision. Produce either (a) a checked constructive
acceptance-to-discharge result, with exact source correspondence and all
remaining original-interpretation premises stated, or (b) a concrete reachable
ordinary acceptance trace with a generated obligation that is omitted,
unresolved, or not discharged. Such a trace refutes the parent only if it is
independently connected to failure of an original source judgment. Do not
equate `Ok` with parent `solves`, define `solves := Satisfies`, assume a
readback/witness, or narrow the parent source domain.

The source lane is read-only and must inspect at least the solver path and its
actual ordinary consumer/acceptance owner. Luna's bounded tracked call-site
search identified `tools/inference-playground/src/lib.rs` as an ordinary
consumer candidate. The lane may use read-only `git ls-files` solely to
confirm this exact path is tracked; content searches are limited to frozen
owners below. If another consumer or constraint owner is outside them, stop
and return the exact path for Luna to pin under a sequential contract revision. Record
NO_SAFE_CODE_SLICE unless a concrete defect under approved semantics is
demonstrated. No production promotion follows from this sprint.

## Frozen baseline and direct inputs

- Branch/base: `yulang3`, commit `6a7e31c39`.
- `crates/yu-solver/src/lib.rs`:
  `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`
- `crates/yu-solver/src/scc.rs`:
  `8f3709ec9d52dc79767b6822eb4f671118a3f83814d2e9a9c748dfeac51e1f72`
- `crates/yu-solver/src/f5c_generalization.rs`:
  `928607961bff9ab747fd759aed1dacd3aa13abc9e20bf3bb8a957a4c7bd12ffb`
- `crates/yu-solver/src/f5c_replay.rs`:
  `71fb166c38dbd93571abcbc3ff290b3b79fe2a4ecba8159edd5f60933c8b3b2a`
- `crates/yu-types/src/lib.rs`:
  `fb3d53cdcce6a2d7149508ba0bdc9dad643cfc795fefdb9914afcb461e4aa6d8`
- `tools/inference-playground/src/lib.rs`:
  `45bf78af436efa50e02ca97ba3b639c11f7dd88272d87c47f2822643786653d4`
- `notes/theory/lean/YulangClosure/Contracts.lean`:
  `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `OriginalSourceInterpretation.lean`:
  `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`
- `OriginalParameterSemantics.lean`:
  `733c5b05e0db226f95d14ff2161c46e9a389b43d86b365b000a9656ec4fd0bd2`
- `OriginalParameterWorld.lean`:
  `7b5f849f744dbe56f374d8be6b11a5a218176abf6eeda2fb9da8180c7b1ff802`
- `InferenceConstruction.lean`:
  `576d69266da62c0f75fa9748ff0f0691a9f0bc3aca5148be9d25cef82d2010f0`
- `OriginalProofProgress.lean`:
  `21e361962538d5e2738041b58186682a4a9fb3ad10c75f4c39dc97e32a443f39`
- `OriginalSourceGeneration.lean`:
  `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `OriginalSourceSyntax.lean`:
  `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
- `OriginalSourceChecking.lean`:
  `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`
- `docs/yulang-source-type-safety-ja.tex`:
  `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`
- `docs/yulang-semantics-and-soundness-ja.md`:
  `2a0b173406353524950e1ab690c679918185167e63929c9b6724547b5cd379f2`
- `docs/yulang-whole-proof-closure-ja.md`:
  `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`
- `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`:
  `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`
- `notes/design/2026-10-24-birth-level-scc-intrusion.md`:
  `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`
- `notes/design/2026-10-08-source-generalize-definition.md`:
  `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`
- `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`:
  `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`
- R175 contract rev7:
  `db9e77b97ec86ef32e8de0ababc3b5daa25ef09d4b961cbe8153c4a5cb0f22ca`
- R175 reviewed integrated outcome:
  `7c3f30d1938c10ccd843c153aae10665552c8d123d999b4de4769af4cc03621c`
- Authoritative inference principles:
  `notes/design/2026-10-11-yulang-inference-top-level-principles.md`
  SHA-256 `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.

Verify every listed hash before content reads. Preserve the R175 source/effect
boundary: permission, actual inflow, and subtraction residual remain distinct.
Do not inspect runtime/machine paths, pending questions, or quarantined paths.

## Leases and lanes

- Source lane: registered `researcher`, 900 seconds. Read-only tracked-call-site
  search and frozen source trace. Sole output lease:
  `tasks/agent-loop/inbox/ordinary-solution-adequacy-r176-source.md`.
- Constructive proof lane: registered `lean_prover`, 1200 seconds. Sole output
  leases:
  `notes/theory/lean/YulangClosure/OrdinarySolutionAdequacyR176.lean` and
  `tasks/agent-loop/inbox/ordinary-solution-adequacy-r176-proof.md`.
  Construct only from authenticated source equations and the frozen original
  definitions. A conditional/model-relative result must label every supplied
  premise and apply the useful implication to the original parent immediately.
- Fresh independent reviewer: 300 seconds after both lanes stop and the exact
  outputs/dependencies freeze. Luna alone integrates and assigns review.

Proof/cache ownership belongs only to the proof lane. It may use the already
installed Lean 4.35.0 and existing `notes/theory/lean/.lake`; do not create an
environment/cache or update packages. Any delivered theorem must be checked in
the pinned project with complete theorem types and axiom audit. At most one
focused check plus its required import build, 1 CPU, 1 GiB per process, 180
seconds total; do not run the default/full build unless a separate contract
revision authorizes it. If cached dependencies are missing or checking would
create substantial new state, stop and report the exact blocker.

No Rust edits, Cargo, tests, runtime execution, scratch output, generated
environments, or additional paths. Preserve all UNKNOWN rows and quarantines.
Stop at the first unpinned owner, semantic ambiguity, reachable counterexample,
resource limit, or need for changed compiler behavior.

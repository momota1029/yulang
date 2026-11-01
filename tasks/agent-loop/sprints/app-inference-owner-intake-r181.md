# Sprint R181 — App inference owner-definition intake

Status: admitted bounded continuation of the unchanged Yulang type/effect
inference-soundness goal. Baseline: `yulang3` at
`3529921c1eef91cc692a6ec9f821316486b45ebf`.

## Parent and fixed scope

The parent remains original `SourceProblem.InferenceSoundness`: every supported
source, generated constraint set and satisfying solution must yield the original
source typing judgment under that same solution and the one shared
`sameScoped` witness. Preserve all source forms, quantifiers, effects, original
admission, and complete telescope.

This sprint prepares an owner-facing definition proposal for the missing App
inference-result/readback equation. It does not adopt new source semantics,
change compiler behavior, claim a proof, or imply that Rust implementation
correctness proves Yulang typing soundness.

## Fixed outcome

Produce a concrete proposal and an authenticated authority map that separates:

1. equations already determined by accepted original source semantics;
2. the precise equation or semantic choice those sources leave unspecified;
3. the required operands and outputs for an App inference result and its
   readback under solution `a`; and
4. the exact unchanged `generates`, `solves`, original App admission, and
   `sameScoped` consumer that a later proof must satisfy.

The proposal must retain the actual callee and whole inert argument, complete
prior telescope, descriptor/interface endpoints, selected occurrence and
payload, and one same-assignment joint witness. It must not make admission an
output premise, strengthen `generates`/`solves` until the conclusion is
immediate, substitute a consumer iff, or introduce a fresh/per-field witness.

If the accepted sources do not determine the construction equation, present it
as a design decision with exact alternatives, required authority, and its effect
on the unchanged parent theorem. Do not choose or implement that policy here.

## Required intake questions

- What is the source-owned App inference object, including its complete image,
  descriptor/profile fields and selected interfaces?
- How is that object read back at one satisfying assignment into the original
  App `Logical` payload and unchanged `LocalAdmissions.logical` judgment?
- Which child judgments, whole-inert-argument rule, telescope extension, and
  assignment/joint witness are shared by construction and readback?
- Which clauses determine each equation, and which remain a semantic choice?
- How does the proposed object enter the existing `SourceProblem.generates`,
  `solves`, and `sameScoped` definitions without changing their claim?

Return exact citations and a line-by-line authority matrix. A proposal is useful
only if it identifies a constructible proof target after the source owner
accepts or confirms the equations.

## Frozen direct inputs

Before content reads, require these 16 exact path rows, each with one full
64-hex SHA-256. Recompute every digest. A mismatch or newly cited owner stops
for sequential primary admission. Existing R180 claims may be used through the
frozen reports; do not repeat their broader source search.

- `tasks/agent-loop/sprints/app-descriptor-formation-r180.md` —
  `5f6993f5ecfa977b3fac347ff78ea31c3b953e76c98b58af98ed3a4d08d40055`
- `tasks/agent-loop/history/app-descriptor-formation-r180-activation.md` —
  `60dc885917610fa142f7aab662373ead0b49883ab482c25a35e97330c1aef6bc`
- `tasks/agent-loop/history/app-descriptor-formation-r180-outcome.md` —
  `4396f2a2348a3a1810c3fa0f51b47ef19e6484ce02ed662c3706605ea3c6a273`
- `tasks/agent-loop/inbox/app-descriptor-formation-r180-proof.md` —
  `9e54b2c3bf1edc7bc0f5854e9dbaa0a54522cd4dad7d67bea6d660362672e6ea`
- `tasks/agent-loop/inbox/app-descriptor-formation-r180-source.md` —
  `286d2a9137d8a539ecf082276fa14506b69d5f23a164811668a3ff606f71fa66`
- `notes/design/2026-10-02-typed-computation-core-elaboration.md` —
  `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e`
- `notes/theory/2026-10-07-call-input-construction-proof.md` —
  `f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6`
- `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` —
  `568bb4649ba278519f3ad01af2091dd1baaca42850cd19e3b5734b3c47c2eefe`
- `notes/design/2026-10-02-parametric-component-linking.md` —
  `108fb9ab91c79aedc716ae476a07d567447644892ae1e32671c8fa4bce96efca`
- `notes/theory/2026-10-08-call-source-interface-construction.md` —
  `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98`
- `notes/design/2026-10-05-source-contracts-and-common-allowance.md` —
  `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186`
- `notes/theory/lean/YulangClosure/Contracts.lean` —
  `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` —
  `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` —
  `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`
- `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` —
  `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`
- `notes/theory/lean/YulangClosure/OriginalSourceChecking.lean` —
  `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`

## Lanes and limits

- One registered `researcher`, 600 seconds, read-only source/type-theory
  authority intake; sole exact leased output:
  `tasks/agent-loop/inbox/app-inference-owner-intake-r181.md`, containing both
  the concrete proposal and authority matrix.
- Fresh independent exact-conformance review: 300 seconds after outputs freeze.
- No proof worker or Lean command until the defining equations are authenticated
  and a constructive theorem target exists. No Rust inspection, implementation,
  tests, builds, runtime, Cargo, scratch, or environment/cache creation.

Luna retains exact leases, review, adjudication, records, staging, commit and
push. Preserve all UNKNOWN rows and quarantined paths. Parent remains OPEN.

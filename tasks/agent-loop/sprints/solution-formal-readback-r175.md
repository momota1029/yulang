# Sprint R175 — same-solution readback preflight (contract revision 3)

Status: ADMITTED under the unchanged Yulang type/inferred-effect
soundness goal. Runtime/machine correctness is excluded. Baseline: `yulang3`
at `59fce5ec0`; Luna owns integration and Git.

## Parent and fixed outcome

The parent remains `YulangClosure.SourceProblem.InferenceSoundness`
(`Contracts.lean:127–130`), with its original quantifiers/source domain and one
shared `sameScoped` witness. R174 is closed with independent PASS for
`BLOCKED_SOLUTION_CARRIER`; the parent remains OPEN.

Determine whether the existing authoritative source semantics and actual
inference carrier determine a pre-invocation `FormalAssignment` readback from
the *same* successful solution. Value must read an original `Descriptor` from
the prepared `native_root`; Computation must read the complete original
`Interface` from `native_root` plus `entry_effect`, under the original prior
telescope and source coordinate. Do not stipulate `solves := Satisfies`,
carrier identity, or an assumed readback function. `Ok(...)` alone is not the
success relation because returned results retain errors.

This sprint is an admission preflight. Its output is either a frozen exact
input set ready for a constructive readback sprint, or
`BLOCKED_SEMANTIC_AUTHORITY`, naming the first missing original definition and
required authority/input. It creates no conditional lemma and claims no parent
closure. If authority is present, Luna admits the theorem construction as the
next exact packet and applies it to R173's missing premise.

## Frozen inputs

R174 contract v4 and reviewed source handoff are immutable dependencies:

- `tasks/agent-loop/sprints/solution-carrier-identification-r174.md`:
  `72425107a3ad4d71844f666b2ff3fd2eefa4b34e26dd53f3737c0d2ee9430e79`
- `tasks/agent-loop/inbox/solution-carrier-identification-r174-source.md`:
  `8e653a67c593a8ccffe459f549f3d865784e36b56cc3112b5f4b26cb6c435ad2`
- solver API owner `crates/yu-solver/src/lib.rs`:
  `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`
- candidate owner `crates/yu-solver/src/shadow_apply.rs`:
  `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5`
- public candidate observer owner `crates/yu-solver/src/candidate_call.rs`:
  `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`
- feature manifest `crates/yu-solver/Cargo.toml`:
  `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`
- `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `OriginalSourceInterpretation.lean`:
  `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`
- `OriginalParameterSemantics.lean`:
  `733c5b05e0db226f95d14ff2161c46e9a389b43d86b365b000a9656ec4fd0bd2`
- `OriginalParameterWorld.lean`:
  `7b5f849f744dbe56f374d8be6b11a5a218176abf6eeda2fb9da8180c7b1ff802`
- `OriginalFormalAdmission.lean`:
  `77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c`
- `OriginalSourceEnvironment.lean`:
  `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`
- `InferenceConstruction.lean`:
  `576d69266da62c0f75fa9748ff0f0691a9f0bc3aca5148be9d25cef82d2010f0`
- `OriginalProofProgress.lean`:
  `21e361962538d5e2738041b58186682a4a9fb3ad10c75f4c39dc97e32a443f39`
- R173 proof/source handoffs:
  `8666a46cca3e2d20f01a6cdff64cc67616c3840fbb394679dc6829a032a1749d`,
  `c07c17baaf32608a4ce526686b17ede584912fb717d7d5ca510b50fea487fe17`

Verify hashes before reading. If caller or semantic owner evidence requires a
path outside this set, stop and return its exact path for primary pinning.
`candidate_context.rs` is not preauthorized; pin it only if the selected
construction demonstrably consumes that representation.

Revision 2 adds `candidate_call.rs`, after the source lane identified it as
the first owner needed to inspect the candidate route's formal observer. This
is a read-only dependency; no result claim or write authority changes.

Revision 3 pins the original semantic authorities that the proof lane found
necessary to interpret `Descriptor`, `Interface`, effect membership and the
scope/witness contract. Luna had hashed these files before a bounded authority
orientation read; no worker read them under revision 1 or 2:

- `notes/design/2026-10-08-source-generalize-definition.md`:
  `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`
- `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`:
  `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`
- `notes/design/2026-10-08-contextual-function-membership-definition.md`:
  `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0`
- `notes/theory/2026-10-08-call-semantic-input-realization.md`:
  `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a`
- `notes/theory/2026-10-08-simultaneous-immutable-root-introduction.md`:
  `a5efa7056b12f931892548ecf3366d66156627ec44577c99d20ca48596438ae6`
- `notes/design/2026-10-05-inferred-function-call-views.md`:
  `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1`
- `notes/design/2026-10-05-source-contracts-and-common-allowance.md`:
  `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186`
- `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md`:
  `f11c6594e43c29fbfdbca1638b5c548cecc12a5beb192cac743e60f022c1cc73`
- `notes/design/2026-10-02-source-result-synthesis-choice.md`:
  `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992`
- `questions/2026-10-05-source-annotation-boundaries/approved-answer.md`:
  `e1e2ff77b181fe42edd404ee0d69cfc6d3bb0fbc99ba7e7f092710025d11fb12`
- `notes/progress/2026-10-08-source-generalize-review.md`:
  `dcb73203e4b5b845e401f8705fbd1fc513b3791595120fa2db5fac94b7df6b5b`
- `notes/progress/2026-10-08-call-interface-admission-review.md`:
  `b679ebc836cc3691854a243444595e5a8f35116a0766503886eebc65a1eb07c4`

These documents may define source-side contracts, but do not license equating
Rust solution state with them. If their authority points to another required
correction, stop and return its exact path before reading it.

## Read-only lanes

**Source lane:** registered `researcher`, 600 seconds. Trace which solver
return is the ordinary inference API and which is feature-gated/research-only;
inspect public callers, result/error semantics, and prepared Value/Computation
formal endpoints. Use only frozen Rust inputs and exact existing R173/R174
handoffs. This is read-only; send findings to Luna for the single integrated
handoff.

**Proof lane:** registered `lean_prover`, 900 seconds. Audit whether the frozen
original semantic modules define a concrete `Sorts`/`SourceProblem` instance
and whether it interprets the same Rust solution, descriptor, interface,
assignment, inherited scope, effect membership and joint witness. This is a
read-only definition/authority audit: do not write a theorem or Lean module.
Send theorem types, exact authority findings and any first blocker to Luna for
the single integrated handoff. If a theorem is available, Luna assigns it in a
separate exact construction packet with complete theorem/axiom review.

**Primary write lease:** Luna alone writes
`tasks/agent-loop/inbox/solution-formal-readback-r175.md`, integrating both
read-only lane results. No child write leases are granted.

No Rust edits, runtime/machine inspection, tests, Cargo, environment/cache/
target/scratch creation, or production promotion. No worker descendants. Stop
at the first missing authority or unpinned owner. Preserve all UNKNOWN rows and
quarantines.

After both writers stop, assign a fresh independent 300-second reviewer for
the exact frozen outcomes and hashes. Only Luna integrates, stages explicit
paths, updates state and pushes a reviewed coherent checkpoint.

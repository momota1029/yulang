# Sprint R174 — identify the actual solution carrier

Status: ADMITTED under the unchanged goal: Yulang type and inferred effect-row soundness against original source typing rules. Runtime/machine correctness is excluded.
Branch / baseline: `yulang3` / `bb9b5826a`. Luna owns integration and Git.

## Parent and admitted outcome

The parent remains `YulangClosure.SourceProblem.InferenceSoundness` in
`Contracts.lean:127–130`, with every original quantifier/source form and the
same single `sameScoped` witness. R173 was independently reviewed and found the
first missing semantic input: constructing the original pre-invocation
`FormalAssignment` from the *same actual solution* and prepared native fields.
Value needs the original descriptor from `native_root`; Computation needs the
original complete interface from `native_root` and `entry_effect`.

Before another formal construction, identify what the actual returned solver
result `a` is, how it retains the constraints/solution, how callers obtain
inferred types/effect rows, and whether any existing original source model
assigns this result a descriptor/interface interpretation. Do not stipulate
that `a = SolvedModule`, `generates = Build`, or `solves = Satisfies`. A precise
`BLOCKED_SOLUTION_CARRIER` result is success if the concrete representation or
source interpretation does not exist. No new conditional theorem is authorized.

## Read-only source lane

Owner: registered `researcher`, 600 seconds. Inspect only the pinned Rust
solver result owner and closed-type representation, plus the frozen R173
handoffs and pinned Lean parent/source definitions. Trace the actual public
solve return, retained internal state, public projection/scheme accessors,
value/effect encodings, and any bridge from those values to the Lean
`Solution`, `Descriptor`, `Interface`, and shared witness. Distinguish the
internal worklist state from the published result and from user-facing type
observations. No runtime path.

Write lease: only
`tasks/agent-loop/inbox/solution-carrier-identification-r174-source.md`.
No Rust edits, Lean edits, builds, Cargo, tests, Lean invocation, cache,
environment, target, scratch, Git, or descendants. Stop at the first missing
carrier or interpretation equation. Report `NO_SAFE_CODE_SLICE` if no approved
Rust defect is demonstrated.

## Frozen inputs

- `crates/yu-solver/src/lib.rs`: `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`
- `crates/yu-types/src/lib.rs`: `fb3d53cdcce6a2d7149508ba0bdc9dad643cfc795fefdb9914afcb461e4aa6d8`
- R173 contract rev2: `a67521efc53a0ac98af0e91414fd6cd58e7cfa9ab06f89a0d5d5149479f40078`
- R173 proof handoff: `8666a46cca3e2d20f01a6cdff64cc67616c3840fbb394679dc6829a032a1749d`
- R173 source handoff: `c07c17baaf32608a4ce526686b17ede584912fb717d7d5ca510b50fea487fe17`
- `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `OriginalParameterWorld.lean`: `7b5f849f744dbe56f374d8be6b11a5a218176abf6eeda2fb9da8180c7b1ff802`
- `OriginalFormalAdmission.lean`: `77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c`
- `OriginalSourceEnvironment.lean`: `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`

Verify every hash before reading. If a needed representation owner is outside
this set, stop and return its exact path; Luna will pin it before further work.

## Review and stop boundary

After the handoff freezes and the source writer stops, Luna assigns a fresh
independent read-only reviewer (300 seconds) to verify the carrier trace,
public/internal distinction, exact hashes and blocker. No production authority
or semantic change follows. Preserve all UNKNOWN rows and quarantines. The
reviewer cannot be the source author. Only Luna stages/commits/pushes reviewed
artifacts.

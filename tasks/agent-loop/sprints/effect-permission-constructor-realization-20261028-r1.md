# Sprint EFFECT-PERMISSION-CONSTRUCTOR-REALIZATION-20261028/r1

Status: CANDIDATE pending primary admission. It continues the unchanged broad
Yulang inference/executor soundness goal.

Branch: `yulang3`. Integrated baseline: `6f9d7314f`.

## Original outcome and success evidence

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1, 3, 5, with its original quantifiers and source domain unchanged.
Preserve the approved effect hygiene meaning in
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–5:
contravariant `[E]` grants local subtraction permission, only actual handler
inflow is subtracted, symbolic dependencies remain, and independent same-row
lineages remain distinct. A/B, whole-language soundness, principality,
progress, termination, source/native and production gates remain OPEN.

Sprint outcome: strengthen the actual successful-constructor to
source-approved capture/export path. The Rust lane gives each capture an
identity and authenticates the owner/domain join through ordinary
`CandidateInference::solve`, definition export and `formal_effect_permissions`.
The Lean lane repairs the prior final-check failure, audits every delivered
theorem, and derives `Origin` and allocated-row evidence for the modeled
constructor transitions. Both lanes retain an explicit exact transition where
the real row/bound/evidence/context recurrence or canonical transport is still
unsupported.

Success evidence is either (a) a checked constructor-derived origin result plus
an independently authenticated source crosswalk for memo-hit, memo-miss and
delegated-allocation cases, with owner-identified capture/export joins, or (b)
the exact first successful source transition that the current model cannot
represent, recorded with the strongest preceding checked result. Finite tests
do not prove universal correspondence. A source-approved transition that
cannot decode to the modeled origin, or a successful wrong-image export that
preserves occurrence/path, falsifies the proposed relation.

No source restriction, semantic weakening, solver/preflight/recovery/API change,
expected-output change, or production approval is authorized.

## Frozen inputs

- `candidate_effect.rs`: `7c8e4fe5270fd45cecece80dfbbdff81aa8f294546687938bf89212325fc146b`
- `candidate_scheme.rs`: `35c58dca3748595e273cd53bfba07da2be3fd340ec63c56f6a18adea5e514fb1`
- `shadow_apply.rs`: `2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d`
- `yu-solver/Cargo.toml`: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`
- failed final `FormalPermissionSourceOrigin.lean`: `3e8ae8ba21cdaf47e1172a40d69f37a29247d2987a323e0c0746e7770ac58231` (preserve in Git history and scratch before editing)
- `FormalPermissionLiveCapture.lean`: `0e1bd4f2ae95e798561e014595e66ec9b6d9b342dbd2b15d0d5c9d346838c53e`
- `FormalPermissionCaptureConstruction.lean`: `181d5075e2fa3ed5f4adfe4029b368461638b6ac6f62341ec165e6e3980ee13c`
- `OriginalEffectHygiene.lean`: `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f`
- `WholeMetatheory.lean`: `65777d3da4fb2a28b25e961049afb88f3ed750c30d04ae73bdc907ef5f93de26`
- annotation authority `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`; inference principles `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`; original parent `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`
- toolchain `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`; lakefile `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`; **correct** manifest SHA `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.

The preceding sprint contract's manifest typo is preserved and adjudicated in
its outcome; no dependency mutation was found. Preserve all unknown runtime
writer paths and quarantines.

## Proof lane — registered `lean_prover`

Sole repository leases:

- `notes/theory/lean/YulangClosure/FormalPermissionSourceOrigin.lean` (fresh
  revision; preserve prior committed bytes in Git and copy failed source/logs
  to immutable scratch before any edit)
- `notes/theory/lean/YulangClosure/FormalPermissionConstructorRealization.lean`
- `tasks/agent-loop/inbox/effect-permission-constructor-realization-proof.md`

Scratch only: `/tmp/yulang-effect-permission-constructor-realization-20261028-r1/lean-project/`.

Stages: repair the exact contradictory `none` branch and compile; print complete
types and transitive axiom audits for all 12 delivered declarations on the final
hash; then extend the model with a decoder/refinement from actual successful
constructor events. Model scoped memo hits/misses, delegated allocations,
metadata/path and allocated-row witnesses. Derive `Origin`, do not assume it.
Relate model events to Rust's frozen source crosswalk without asserting that
abstract histories are exhaustive. Keep row/bound/evidence/context recurrence,
canonical representative transport, concrete LIFO node writes, endpoint
arrival and export membership explicit. Use at most three serialized
single-process Lean/helper invocations total, sharing at most 180 seconds;
one CPU, <=1 GiB RSS per process. Preserve every failure. No retry after the
three-invocation limit; no root/default-target integration.

## Rust lane — Luna/high `implementer`

Sole repository leases:

- `crates/yu-solver/src/candidate_effect.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `tasks/agent-loop/inbox/effect-permission-constructor-realization-rust.md`

Scratch only: `/tmp/yulang-effect-permission-constructor-realization-20261028-r1/rust-target/`.

Add only `#[cfg(test)]` observation data needed to give every capture an
explicit identity and correlate constructor emission, root publication, graph
owner, and exported permission. Exercise the required memo-hit, memo-miss and
delegated-allocation branches through ordinary preflight/solve/definition
export. If a source case refuses, preserve exact owner/stage and stop that
case; never bypass or modify preflight. Keep disabled instrumentation dormant
and lazy. Do not change solver choices, recovery, API, behavior, expected output
or language semantics.

Freeze sources and exact command before one focused Cargo invocation. Retain
raw stdout/stderr, exact argv, exit, wall time, peak RSS, CPU and start headroom
in the leased scratch and handoff. At least 4 GiB available at launch; one CPU,
<=2 GiB RSS, <=180 seconds. No retry. Stop on an unsupported owner, source
refusal, changed dependency, behavior change or resource violation.

## Independent review and resources

After both lanes freeze, assign a fresh read-only non-author
`compiler_referee`. Review the source/event ownership join, branch coverage,
preflight route, test-only instrumentation boundary, Lean final hashes, all
theorem types and transitive axioms, and whether the decoder assumes its target
conclusion. Preserve exact remaining source transitions and all original
parent gates.

Total envelope: **2,700 seconds** — Rust 600, Lean 1,200, review 300, primary
200, dispatcher 100, contingency 300. Two producer assignments maximum, zero
Astra. One heavyweight Cargo process and three serialized Lean/helper
invocations as above. Only the primary updates current state, adjudicates,
stages exact paths, commits and pushes. Next dispatcher trigger: material source
counterexample/blocker, dependency/lease/resource change, integration seam, or
sprint end. Worker STOP leaves no unknown lease silently reusable.

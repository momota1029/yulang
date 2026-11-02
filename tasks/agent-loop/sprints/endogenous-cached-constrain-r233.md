# Sprint R233 — endogenous cached constraining

Status: **ADMITTED; proof in progress**. Branch `yulang3`; baseline
`d47635c57d3c34099da999dc41f2475ce202be5a`.

## Fixed goal and parent accounting

The unchanged roots remain `Contracts.SourceProblem.InferenceSoundness`,
`SourceScopedCoverage`, `PrincipalCoverage`, and `InferenceTermination`, with
their original quantifiers and source scope. R233 does not activate or narrow
any of them. Its outcome is to reduce a first-order algorithm-definition gap
on the path toward those roots: define the mathematical constraining operation
with its own comparison cache, opposite-bound replay, and structural
decomposition, then prove the soundness obligation for the actual operation.

The selected source is the frozen Parreaux Simple-sub import: §3.2.2 / Fig. 9,
with sound-constraining proof architecture in §5.3.1, Lemma 2. Yulang's
authoritative inference principles continue to govern both value and effect
ports, extrusion, occurrence-qualified intrusion, and generalization. No
source-local `Kernel`, `Build/Satisfies`, Rust observation, successful-run
certificate, or arbitrary readout may be used as a premise to make the
transition appear complete.

## Exact work and evidence

1. Freeze the paper-faithful cached `constrain` state/transition and its
   comparison-cache invariant. The cache is mathematical state used to control
   recursive constraint comparison; it is not a new filesystem build cache.
2. Relate R229's actual upper-insertion branch to the corresponding operation.
   Add the dual lower insertion, replay of retained opposite bounds, and
   recursive Function/Record/Tuple/Variant decomposition only where their
   source equations are present. Keep the Function's four distinct
   `(-,-,+,+)` ports and Value/Effect kinds.
3. Prove that every successful result of the modeled operation preserves the
   source's consistency/subtyping obligation, including cache-hit and cyclic
   cases. State every invariant used by the induction; do not assume the
   desired theorem in a renamed hypothesis.
4. Apply the result to the unchanged soundness root only if its hypotheses are
   actually produced by the unchanged root's generated constraints and
   solution. Otherwise report parent delta zero and the first missing equation.

Falsifiers: lower/upper insertion activating a previously latent comparison;
a two-variable comparison cycle revisiting a cache entry;
recursive Function demands using all four ports; extrusion followed by SCC
equality and propagation. A cache hit that skips a necessary structural branch
or replay refutes the proposed invariant.

Success is a checked theorem for the exact operation plus its application to
the original parent, or a precise first missing equation that materially
shortens the critical path. A finite externally supplied history, cache-free
partial operation, conditional restatement, source-rule reconstruction, or
local lemma without parent application is not a closed root.

## Lanes, leases, and limits

- Proof author: one registered `lean_prover`, exact outputs
  `notes/theory/lean/YulangClosure/AbstractCachedConstrainR233.lean` and
  `tasks/agent-loop/inbox/endogenous-cached-constrain-r233-proof.md`.
- Independent reviewer: fresh nonauthor `compiler_referee`, read-only; exact
  output `tasks/agent-loop/inbox/endogenous-cached-constrain-r233-review.md`.
- Luna owns this contract, `current.json`, adjudication,
  integration, and Git. Do not touch other dirty or quarantined paths.
- Implementation lane: `NO_SAFE_CODE_SLICE`, based on the inspected R230
  owners; no Rust changes. Native simulation and production remain separate.
- No new worktree, environment, target directory, or build cache. If Lean
  verification is needed, Luna alone writes the existing
  `notes/theory/lean/.lake/build` after the author freezes source outputs. The
  author does not invoke Lake or write cache paths. Cap additional apparent
  `.lake` growth at 64 MiB; no cache cleanup. At most 1 CPU, 1 GiB RSS, 180
  seconds per Lean invocation, 1,200 seconds aggregate proof work, and 600
  seconds independent review. No Cargo, default Lake build, or tests.
- Dependencies (frozen at admission):
  - `AbstractSimpleSubCore.lean`: `023635d283f9a00e906ec965a6eaa5595eab21f2b93f353a1d5ea0ede0bffb6c`
  - R229 module: `8f2132e050ea6a0de47eb7da3685d6116d8aedf64d59b02b399204d96735946a`
  - R230 module: `ee16a4e68bb6357a51877a83e78239db08a0789eecd090f387760db2c2632a50`
  - paper/source import: `cd2b84a84d16be8856766f0514a2f400cf224ac95b6e81e42d4a7a875036e113`
  - inference principles: `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
  - root-first plan: `890fa8a5a1c88c6400e293870598750b285fe12075ad13cbd3e884cc71921c16`

Stop on a source-equation mismatch, counterexample, missing authoritative
transition, dependency drift, or resource cap. Preserve every failed checker
receipt. No semantic adoption or production promotion is part of this sprint.

## End state required

Record the exact transition and theorem types, full axiom audits for checked
declarations, parent application/delta, counterexamples exercised, limitations,
review result, all cache paths and growth, and writes-stopped evidence. Keep
all four roots and five packages open unless a reviewed proof actually closes
one in its original scope.

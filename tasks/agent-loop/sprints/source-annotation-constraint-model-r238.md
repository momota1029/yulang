# Sprint R238 — source annotation constraint model

Status: ADMITTED, primary-owned source/model construction prerequisite.
Baseline: `ee5977573c045088d9f5f12883393e522fec4a96` on `yulang3`.
Goal: continue Yulang type-inference guarantees, prioritizing the already
selected effect-hygiene policy and eventual application to
`YulangClosure.SourceProblem.InferenceSoundness`
(`notes/theory/lean/YulangClosure/Contracts.lean:128–130`).

## Fixed semantic scope

Preserve the original Simple-sub/source claims and quantifiers. Use the
authoritative annotation policy in
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–5:
composed polarity; contravariant concrete effects are local subtraction
permission, covariant concrete effects are allowances; permissions, actual
inflow, symbolic dependencies and residual effects remain distinct.

Do not change source semantics, supported forms, generator behavior or parent
theorems. Do not claim a full `SourceProblem` instance exists. R217's
`SourceAnnotationElaborationR217.Declaration` and resolution are source-model
candidates; R208's profile classification is existing mathematical machinery.
Connect them only through explicit definitions and checked equations. Preserve
the distinction between an `Effectful` wrapper effect row and direct Function
arrow rows; R218's two external readouts are a falsifier, not authority.

## Required construction

Construct the following source-owned chain from the actual original Lambda
formal and a resolved immutable declaration, without using a chosen typing,
solver result, source judgment, `Kernel.atom`, or an external annotation tree:

```text
original Lambda formal + declaration environment
  → resolved declaration at the same annotation/owner/scope
  → independently generated annotation clauses
  → satisfaction under the same interpreted assignment
  → exact original `sourceFormalRole` atom in `sourceRules`
  → its Lambda `Judgment`/`Build` consumer
```

Retain owner, scope, formal entry kind, annotation identity, row path and source
positions. Show the four-port/polarity mapping, and keep effect wrapper rows
separate from Function argument/result arrow rows. If the source declaration
environment, assignment interpretation or exact Lambda consumer cannot be
defined from existing authoritative source structures, stop at that boundary
and record the precise missing equation. Do not assume a reflection theorem to
make the diagram commute.

This packet is a prerequisite model construction, not a Lean proof-lane
activation. Parent-premise delta remains zero unless a checked result applies
to an exact original Lambda local premise. Do not expand into permission,
arrival, residual, all-source soundness, principality, termination or Rust
implementation proofs before that consumer is real.

## Evidence and leases

Baseline and direct dependency hashes are frozen at admission:

| Path | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fecf3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `notes/theory/lean/YulangClosure/SourceAnnotationElaborationR217.lean` | `e10a84fc095af0cd492f1dd8285eb0136f185b64a29a66deaddc35973c6c08d3` |
| `notes/theory/lean/YulangClosure/StaticAnnotationConstraintInterpretation.lean` | `1829ee637ab5cf3254e220e4c0fc1306f248499f087baa779287b947c67018c9` |
| `notes/theory/lean/YulangClosure/OriginalAnnotationReconstructionR218.lean` | `757e1aba95e32761360676facdab27ca11b34b4e1b986c8b0f1479ee33a604e6` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

Primary-only exact outputs:

- `notes/theory/lean/YulangClosure/SourceAnnotationConstraintModelR238.lean`
- `tasks/agent-loop/inbox/source-annotation-constraint-model-r238.md`
- this contract and primary-owned `tasks/agent-loop/current.json` state.

No writer is assigned to Rust. At least two clean owners were inspected:
`crates/yu-solver/src/candidate_source.rs` already retains source annotations;
`crates/yu-solver/src/candidate_effect.rs` publishes entry permissions and
authenticates registered-use reads; the receiver's indexed permission checks
also already exist. Current implementation evidence supports
`NO_SAFE_CODE_SLICE`; do not touch the UNKNOWN/quarantined runtime files.

## Resources, review and stop conditions

Use the pinned Lean 4.35.0/Lake 5.0.0 project and the already existing
`notes/theory/lean/.lake` only. No new cache, worktree, environment, `target`,
or scratch directory. Cache growth cap: 64 MiB. Primary construction budget:
2,400 seconds; fresh independent source/model review: at most 600 seconds;
zero Astra. The user explicitly authorized cache generation. No tests are
requested; do not run them.

Falsify the proposed chain if it needs an externally chosen annotation tree,
assumes the desired `Kernel.atom`/admission fact, changes the assignment or
source coordinates, conflates wrapper and arrow rows, drops symbolic variables,
or cannot type the exact original consumer. Stop with the first precise missing
source equation. A conditional theorem, generated formula identity or static
Rust record does not close soundness.

At the end, report the exact theorem types and complete axiom audits for any
checked declarations, the source-to-consumer mapping, what remains missing,
and the parent-premise delta. Freeze the artifact for an eligible nonauthor
review before integration. Luna alone owns Git and any push.

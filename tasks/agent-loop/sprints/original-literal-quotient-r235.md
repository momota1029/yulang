# Sprint R235 — literal readout through subtype equivalence

Status: ADMITTED, primary-owned mathematical model construction. Baseline:
`0d31b1277` on `yulang3`. Parent remains the unchanged
`YulangClosure.SourceProblem.InferenceSoundness` at
`notes/theory/lean/YulangClosure/Contracts.lean:128–130`, with its complete
source domain, arbitrary satisfying assignment and one shared scoped witness.

## Outcome

Investigate whether the R232 failure of syntactic identity readout can be
resolved by interpreting value terms modulo mutual structural `Sub`. Construct
and kernel-check the quotient result for the literal base equations, then
connect it to the actual adopted L1 descriptor/value/Return rule and the
original literal constructor. The quotient is only a candidate interpretation
until the fixed source and algorithm authorities justify it.

The original L1 meaning remains unchanged for all eight payload-preserving
constructors at the same `(q,r,e₀,ξ,ω)`. Preserve separate synthesis,
written-target and final-root endpoints, the syntax-fixed literal value, pure
Return, and all enclosing contextual permission, inflow, residual, Call, guard,
future and conversion obligations.

## Required construction and gate

1. Define the equivalence `a ≈ b := Sub a b ∧ Sub b a` on actual substituted
   value terms and prove its setoid laws from the pinned structural relation.
2. Prove that reciprocal generated bounds imply equality in the quotient for
   every satisfying valuation. Keep `union B B` as a test against accidental
   syntactic equality.
3. Establish whether the selected Simple-sub algorithm actually generates
   each required literal constraint and typed atom/port for all eight original
   forms, independently of source typing and solver output. Do not promote
   R336 K0's four-form submodel as the full generator.
4. Establish that the quotient denotes the adopted original `PaperTypes`
   descriptor/effect carriers without changing their meaning or assuming the
   desired readout. Preserve payload identity for value construction.
5. Apply the resulting local derivation to the literal case of the unchanged
   source-generation / `InferenceSoundness` proof, naming every remaining
   premise.

Success requires all five steps and a fresh independent review before claiming
any parent-premise reduction. A quotient theorem alone is a mathematical leaf,
not soundness closure. If the actual generator equation or carrier map is not
authorized by the fixed sources, stop at that exact equation and report parent
delta 0. Do not add it as a premise, narrow source forms, rewrite `Sub`, or
infer semantics from Rust behavior.

## Fixed authorities and frozen direct dependencies

The user's adopted L1 source rule and the selected top-level Simple-sub
algorithm govern this sprint. R232's reciprocal equations remain an
unvalidated candidate; its `union B B` model refutes direct syntactic
readout. The module must use the existing `SimpleSubConstraintSyntax.Sub`
without changing it.

| Source | SHA-256 |
| --- | --- |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| `SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `SimpleSubRegularSolutions.lean` | `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29` |
| R194 literal boundary | `c922c01283e89c4cb76ee509f9c8c4dc96bc30644568199546f7ccdf0fbb2550` |
| R196 literal generation | `69d551760efc1b40f9235e749c4d2edde3e439b2cb91655495bf1c22d7d55c7c` |
| R220 abstract denotation | `bbd73afe54030cf3e4378a379a58a6836da1b44c9fd227b0bb8b372329f8a254` |
| adopted L1 source rule | `f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8` |
| top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| pinned Simple-sub import | `cd2b84a84d16be8856766f0514a2f400cf224ac95b6e81e42d4a7a875036e113` |

## Leases, resources and review

Luna owns this contract, `notes/theory/lean/YulangClosure/OriginalLiteralConstraintModelR235.lean`,
`tasks/agent-loop/inbox/original-literal-model-r235.md`, current state and the
outcome record. A fresh nonauthor `spec_auditor` reviews source authority,
circularity, all eight forms and exact parent application after the model is
frozen. No theorem worker activates unless the model gate passes. There is no
safe implementation slice at this seam.

Use only the existing pinned Lean 4.35.0 / Lake 5.0.0 project and its current
`.lake`; no worktree, environment, target or cache path. The user authorizes
cache generation. Bound apparent `.lake` growth at 64 MiB. No Rust/Cargo or
general tests. Preserve all UNKNOWN writers, quarantined paths, pending
questions and unrelated dirty files. Primary verification uses the pinned
checker and full declaration type/axiom audit. Construction budget: 2,400
seconds; independent review: at most 600 seconds; Astra budget zero.

End gate records the unchanged parent application, parent-premise delta,
checker and axiom evidence, exact authority hashes, review, cache growth and
unresolved source/algorithm equation. Commit and push only the reviewed,
coherent R235 files and compact state.

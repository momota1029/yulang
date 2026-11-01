# Sprint R166 — native scope representation bridge

Status: **ADMITTED** under the continuing Yulang Rust/Lean soundness goal.
Branch / baseline: `yulang3` / `3d8ba0b91c720cce142c6b0e19984c5efd938360`.
R165 was accepted and pushed at `3d8ba0b91`; parent effect hygiene remains OPEN.

## Parent and target

R165 proves that its cursor evaluator is extensionally equivalent to
`NativeScopeTransformer.Transformer.evaluate` when `Canonical transformer`
holds. R166 narrows that remaining representation gap: define an explicit
order-preserving `u32 -> Nat` encoding and a Lean representation of the private
Rust transformer operations, derive the ordered representation facts for
successful `identity`, `stamp_input`, `protect_body`, `release`, `then`, and
`remap`, establish the finite-list/binary-search membership correspondence
used by `Missing`, then apply the result to R165's `evaluateCursor_equivalent`.

The proof must not claim Lean has executed Rust or formalized `std::slice::binary_search`.
State the source-level boundary: R166's Lean operations model the inspected
Rust branches, with their connection established by the source handoff; the
Rust standard-library search contract is used only on a sorted slice. No
source semantics or solver behavior changes. Keep the whole theorem conditional
on the explicit relation between a successful native value and its Lean
encoding unless that relation is actually derived in the packet.

This packet does not authenticate external support, allocation/state identity,
the real Catch consumer, source attribution, full effect hygiene, original A/B,
principality, termination, or production. It does not consume the pending
typed-Union question.

## Frozen inputs

- `crates/yu-solver/src/candidate_scope.rs`, SHA-256
  `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03`.
- `crates/yu-solver/src/candidate_context.rs`, SHA-256
  `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`.
- `notes/theory/lean/YulangClosure/NativeScopeTransformer.lean`, SHA-256
  `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`.
- R165 Lean module SHA-256
  `07f93963e223a1d8ad55b91fed94f4efe3e73459b94b96e1b7051b41a810bc2b`.
- R165 proof handoff SHA-256
  `8398752890ad0976f5f9d6f9725f62de5b7dbb2a4c53fa5760a32dcd2249a21b`.
- R165 sprint contract SHA-256
  `6b40ab89d3956c4e7967a3c6a303fb4db9597e8f70df6103d4a7bfdee7e15062`.

Baseline HEAD must remain unchanged during the packet except for Luna's
coherent reviewed checkpoint. If any pinned input changes, stop and rebase the
packet before continuing.

## Lanes and exact outputs

### Lean proof — registered `lean_prover`, requested Sol/high, maximum 1800s

Exact write leases:

- `notes/theory/lean/YulangClosure/NativeScopeRepresentationR166.lean`
- `tasks/agent-loop/inbox/effect-permission-scope-representation-r166-proof.md`

Use pinned Lean 4.35.0 and only the existing `notes/theory/lean/.lake` build
output. Prove explicit encoding facts (including order preservation), the
native representation invariant for each modeled successful operation, and
sorted-slice membership/search correspondence. Connect the final result to
R165 without weakening its initial-state domain. Print every public theorem's
complete type and transitive `#print axioms`; no holes, project axioms, new
environment, target, dependency, cache or persistent scratch.

### Rust/source mapping — Luna, maximum 600s, read-only

Exact write lease:

- `tasks/agent-loop/inbox/effect-permission-scope-representation-r166-source.md`

Inspect only the pinned candidate scope owners, R165/R166 Lean owners and
`candidate_context.rs` call sites. Enumerate every private construction path,
`then` merge branch, `remap` collision path, and guard search. Match each Rust
branch to its Lean model and state exactly where Rust standard-library
contracts enter. Do not edit Rust or inspect unrelated dirty/quarantined paths.

### Independent review and integration

After proof and source artifacts freeze, assign one fresh read-only proof
reviewer and one fresh `compiler_referee` for the Rust/Lean mapping, 300s each.
Neither author reviews its own work. Luna alone adjudicates and integrates.

## Resources, stop conditions, and Git

Aggregate ceiling: 3000s; Lean 1800s; source 600s; fresh review 600s; Astra 0.
No Cargo, Rust tests/build, benchmark, new target, or new environment. Keep all
pre-existing dirty and quarantined paths excluded. Stop on a counterexample,
missing source correspondence, semantic decision, changed dependency, lease
conflict, or budget exhaustion. Only Luna stages explicit R166 files after
review, checks the complete outbound range, commits and pushes a coherent
checkpoint; never stage the pending typed-Union question.

# Sprint R165 — native scope evaluator refinement

Status: **ADMITTED** under the user's continuing Rust/Lean soundness goal.
Branch / baseline: `yulang3` / `92b7b726e35476254b4772dc59a7881667e65916`.
Contract revision: 1.

## Parent and target

Advance the effect-hygiene source/native correspondence by establishing that a
successful execution of Rust `candidate_scope::ScopeTransformer::evaluate`
has exactly the finite-set meaning already defined by
`YulangClosure.NativeScopeTransformer.Transformer.evaluate`, for arbitrary
initial input and protection slices, including unsorted duplicates. The Rust
implementation first sorts/deduplicates each input, unions stamped tags, then
merges the sorted initial-protection and transformer-scope streams with two
cursors. It tests inherited protection and the `Missing` predicate against the
normalized **initial** inputs.

The proof must model the actual cursor transitions and prove a prefix/remaining
invariant; restating the final list comprehension or defining Rust evaluation
to be the Lean denotation is not sufficient. Preserve the full transformer and
initial-state quantifiers. Prove extensionally by membership, then establish the
representation facts needed to connect sorted/unique Rust output to the
existing set-membership denotation. Relate constructors, `then`, and `remap` to
the representation invariant only as far as the inspected source supports.

This packet does not prove source attribution, FreshUse support authentication,
allocator/state correspondence, native Catch execution, allocation-failure
behavior, original whole-language A/B, principality, termination, or production
readiness. These remain separate OPEN gates. No source semantics or solver
behavior is changed.

## Frozen baseline and direct inputs

- Rust `crates/yu-solver/src/candidate_scope.rs`, SHA-256
  `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03`.
- Rust caller `crates/yu-solver/src/candidate_context.rs`, SHA-256
  `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`.
- Existing Lean model `notes/theory/lean/YulangClosure/NativeScopeTransformer.lean`,
  SHA-256 `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`.
- Governing scope composition decision:
  `notes/theory/2026-10-15-compose-scoped-release-construction.md`.
- Effect policy:
  `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1.2, 3–5.
- Inference principles:
  `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–5.
- Prior reviewed boundary:
  `tasks/agent-loop/history/effect-permission-scope-transformer-source-bridge-20261102-r144-outcome.md`.
- Prior native consumer and fresh-map findings:
  `tasks/agent-loop/history/effect-permission-real-consumer-20261102-r147-outcome.md`;
  `tasks/agent-loop/history/effect-permission-fresh-map-support-20261102-r145-review-r2.md`.

Before source/proof work, recompute and match all three frozen source hashes.
Any changed dependency, source semantics, write lease, or collision with a
quarantined path returns to Luna. The question about the original typed Union
rule remains pending and is not answered by this sprint.

## Lanes and exact outputs

### Lean proof — registered `lean_prover`, requested Sol/high, maximum 1800 seconds

Exact write leases:

- `notes/theory/lean/YulangClosure/NativeScopeEvaluateRefinementR165.lean`
- `tasks/agent-loop/inbox/effect-permission-evaluate-refinement-r165-proof.md`

The new module imports the existing native-scope model. Formalize the successful
Rust cursor evaluator (including normalization of arbitrary duplicate and
unsorted initial slices), derive a precise invariant for each cursor prefix and
remaining suffix, and prove extensional equality with the existing
`Transformer.evaluate` denotation. Retain the existing constructor, `then`,
and `remap` definitions; no semantic assumption or project axiom is permitted.
Report each theorem's complete type and `#print axioms`. Apply the result to the
unchanged effect-hygiene implementation correspondence and state the first
remaining source/native premise. A local evaluator theorem is not the original
whole-language soundness theorem.

Use the pinned Lean 4.35.0 project and the existing build-output location only;
this assignment is the sole owner of Lean build/cache outputs for R165. No new
environment, worktree, target, dependency, package, or persistent scratch area.
Stay within the proof budget; do not increase memory or retry an exhausted
checker/build invocation without returning to Luna.

### Rust/source correspondence — Luna, maximum 600 seconds

Exact write lease:

- `tasks/agent-loop/inbox/effect-permission-evaluate-refinement-r165-source.md`

Inspect the frozen `candidate_scope.rs` evaluator, constructors, `then`,
`remap`, and the exact `candidate_context.rs` call sites. Record branch by
branch source-to-Lean correspondence, sorted/unique and cursor invariants,
successful-return boundary, guards and allocation errors, and what the evaluator
does not authenticate. Do not edit Rust, tests, expected output, or Lean sources.
Do not inspect or touch the runtime subtree or any dirty/quarantined path.

### Independent review and integration

After both lanes freeze their artifacts, assign one fresh independent
`lean_prover`/proof reviewer for theorem types, checked outputs and transitive
axioms, and one eligible `compiler_referee` for the frozen Rust-to-Lean mapping
if the coherent artifact requires both reviews under M1/M2. Authors do not
review their own output. Luna adjudicates and integrates only after review.

## Resources, stop conditions, and Git

Aggregate sprint budget: 3000 seconds. Lean: at most 1800 seconds. Rust/source:
at most 600 seconds. Fresh independent review: at most 600 seconds. Astra: 0.
No Cargo/Rust build, benchmark, new target, new environment, or additional test
run is authorized or needed by this proof packet.

Stop on a concrete loop/denotation mismatch; a required semantic choice;
missing or changed dependency; source/lease conflict; proof requiring an
assumption that hides a missing source law; review rejection; or budget
exhaustion. Preserve the original Lean theorem and source behavior. A negative
result is recorded precisely; do not weaken the initial-state domain or claim
source/native closure.

Only Luna stages explicit R165 paths, inspects the complete outbound range and
pushes a coherent reviewed checkpoint. Keep all unrelated dirty/quarantined
paths and the unintegrated typed-Union question untouched and unstaged.

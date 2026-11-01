# Sprint R167 — native successful execution correspondence

Status: **ADMITTED** under the continuing Yulang Rust/Lean soundness goal.
Branch / baseline: `yulang3` / `f5af010783f8bd7c748b2e2838078a08283be496`.
R165/R166 are accepted bounded checkpoints and pushed.

## Parent and target

R166 proves the representation and R165 evaluator result for a `Generated`
Lean model value, but deliberately retains the premise that an actual
successful Rust operation has the same encoded fields and maps. R167 attacks
that native relation directly. Model the successful private API call traces
from `candidate_scope.rs` and prove from each transition and recorded output
that its result fields agree with the existing R166 operation model. Apply
R166/R165 only after deriving those fields and the `Generated` relation from
the trace; do not place final encoded-field equality or `Generated` as an
execution premise.

Cover the singleton constructors, ordered `then` cursor transitions, and
successful `remap`. Represent each `FnMut` call by its actual finite sample
trace and call order; do not assume the closure is a pure function. Keep
separate input/scope closure traces even if their environments can interact.
State how the recorded trace induces the finite maps used by R166. Make
collision rejection, neutral omission, retained release tombstones, first
stamp filtering, reserve/overflow error exits, and success-only return
boundary explicit.

Formalize only the mathematical contracts needed for `sort_unstable`,
`dedup`, sorted `windows(2)` collision checks, and
`slice::binary_search`; do not claim to verify Rust standard-library machine
code or the entire Rust program. No language semantics, Rust code, tests, or
expected output changes.

This packet still does not close source attribution, external-state or FreshUse
authentication, actual Catch consumption, original A/B, principality,
termination, or production.

## Frozen dependencies

- Baseline HEAD: `f5af010783f8bd7c748b2e2838078a08283be496`.
- `candidate_scope.rs`: `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03`.
- `candidate_context.rs`: `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`.
- `NativeScopeTransformer.lean`: `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`.
- R165 contract: `6b40ab89d3956c4e7967a3c6a303fb4db9597e8f70df6103d4a7bfdee7e15062`.
- R165 Lean: `07f93963e223a1d8ad55b91fed94f4efe3e73459b94b96e1b7051b41a810bc2b`.
- R166 contract: `85fb9acc51d8e2ce470fc28b4d9054cdea71ecbf28a9edf6f7a751f1201c1037`.
- R166 Lean: `bee9bc1d052d05cc39e43da8614f52d09eac4c117d58b040e4eab3334be25e7f`.
- R166 proof handoff: `2433e4ece6fb5de9a728d57494b9be09ca26e490cc7da5d0873ec9bb4d723d37`.
- R166 source map: `a8bbdebf22c657f26365104f68d62089dbb312967c69b757b186137d591e54e9`.

If an input changes, stop and re-freeze before continuing.

## Lanes and exact outputs

### Lean proof — registered `lean_prover`, requested Sol/high, maximum 2400s

Exact write leases:

- `notes/theory/lean/YulangClosure/NativeScopeExecutionR167.lean`
- `tasks/agent-loop/inbox/effect-permission-native-execution-r167-proof.md`

Use pinned Lean 4.35.0 and existing `.lake` only. Build an explicit finite
source-step/sampling relation for the inspected successful API calls. Prove
operation outputs equal the corresponding R166-generated model outputs and
connect them to R166/R165 without assuming the result relation. Include all
theorem types and complete transitive axiom audits. No holes, project axioms,
new environment/cache/target/dependency, or persistent scratch.

### Rust/source correspondence — Luna, maximum 600s, read-only

Exact write lease:

- `tasks/agent-loop/inbox/effect-permission-native-execution-r167-source.md`

Trace the actual operation branches and closure-call order. State every
standard-library property used and distinguish successful returns from
allocation/overflow errors. Verify the Lean trace relation captures all source
paths without assuming the conclusion. Do not edit Rust or inspect unrelated
dirty/quarantined files.

### Review and integration

After both lanes freeze, assign a fresh Lean proof reviewer and a fresh
compiler/source reviewer, 300s each within the 600s review budget. Luna
adjudicates, checks the full outbound range, and stages only explicit R167
paths.

## Resources, stop conditions, and Git

Total ceiling 3600s: Lean 2400s, source 600s, review 600s, Astra 0. No Cargo,
Rust build/tests, benchmark, new environment, cache or target. Keep all
pre-existing dirty/quarantined paths and the pending typed-Union question
excluded. Stop on a counterexample, missing source contract, unsupported
closure trace, changed dependency, lease conflict or budget exhaustion. Only
Luna commits and pushes a coherent reviewed result.

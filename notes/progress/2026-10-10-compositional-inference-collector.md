# Compositional source collection toward the inference replacement

Date: 2026-10-10
Baseline: `2478fe3f41fe9533dcea143f3bae1bcafa533fb6`
Status: reviewed solver checkpoint; HIR source extension pending resource repair
Authority: current user Simple-sub correction; existing source and candidate contracts
Production cutover: not performed

## Implementation

`crates/yu-solver/src/shadow_apply.rs` now collects nested Lambda, Apply and
Group recipes with a lexical parameter stack. Parameter references retain
their actual monomorphic startup row. `LambdaRecipe` now records an explicit
component or parameter result endpoint, so an inner Lambda returning an outer
formal does not accidentally return its own formal or allocate a proxy row.
Iterative preflight restores lexical scope at each Lambda exit and retains
the existing expression-depth limit of 128 before recursive collection.

The first independent compiler review found one minor owning defect:
`finish()` assumed that all Lambda recipes belonged to top-level projection
order. Nested postorder emission could block its cursor. The repair selects
definition-root recipes for that cursor, retaining source order and deriving
each projected effect from its own live row. It also covers the existing
captured-local nested recipe.

The pending, uncommitted `crates/yu-hir/src/module.rs` extension retains ordered header parameters and lowers them
to nested Lambdas in the existing opt-in application route. Actual canonical
Pattern ML tails, artifact-owned parameter ordinals, lexical resolution and
each parameter's original source key determine the result. Lambda occurrences
are allocated in source order; synthesized Lambdas retain the existing
MissingSource contract. Default and identity-only F5 lowering keep their
existing zero/one-parameter contract.

Once its resource repair closes, this connects the collector to source shapes such as `my apply f x = f x`,
`my const x y = x` and `my compose f g x = f (g x)`. These are implementation
paths identified by source inspection, not runtime acceptance results.
No source-name special case, annotation requirement, registry approval
prerequisite or new Call rule was introduced.

## Remaining replacement work

The candidate still uses its unresolved pure-effect and own-row models. Its
output remains private and cannot be published as production source inference.
Complete Call effects, roles, protection, images, provider/world identity,
independent admission, licensing and futures remain required.

The frozen Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1` application owner
(`crates/infer/src/lowering/expr/tail.rs:535–627`) retains argument evaluation
effects in the Function demand and connects callee evaluation and invocation
output to the application's evaluation effect. Argument-entry policy must
still distinguish Value entry from retained computations.

The next actual implementation seam is effect graph retention through all
four Function children, generalization and fresh use. Current F5 walks only
value rows and replaces effect children with pure extrema. The successor must
use kind-qualified row/binder identities, retain both directions of effect
bounds, compute eligibility through effect dependencies, and restore them with
one substitution memo per use. Structured nonempty effect-family construction
and source protection operators remain separate code responsibilities.
Registry adoption is not a prerequisite for that variable-graph work.

## Review, verification and resource budget

Solver mode: M1, one compiler referee and a fresh repair-delta referee.
HIR mode: M2, compiler referee plus resource auditor for new source-sized
nested output. Convergence requires no accepted blocking/major findings and
closure of the identified projection defect before integration.

Initial frozen solver candidate and default builds passed with
`RUSTC_WRAPPER= cargo check -p yu-solver --features shadow-apply-candidate -j 2 --offline`
and `RUSTC_WRAPPER= cargo check -p yu-solver -j 2 --offline`.
The first attempt without `RUSTC_WRAPPER=` failed before compilation because
the configured sccache returned `Operation not permitted`; bypassing that
wrapper resolved the environment failure.

No tests were added or executed; no workspace-wide suite or runtime inference
probe ran. No benchmarks or measurement samples/processes were consumed.
The lexical scan is bounded by existing depth preflight. Retained recipe
accounting uses `size_of::<LambdaRecipe>`; the projection filter adds one
linear pass with constant space. Header collection and wrapping are linear
in parameter count.

The fresh solver delta referee closed the projection-cursor finding with no
new findings. It also checked the frozen HIR/solver parameter-startup and
recipe-order integration seam. The separate HIR compiler referee found no
correctness finding, but the resource auditor identified a major hazard:
unbounded flat header width creates recursively owned Lambda boxes before
the solver's depth rejection. Only that source extension remains uncommitted;
its owning preconstruction boundary is under bounded architect adjudication.
No HIR gate or broader inference gate is declared complete.

The frozen solver repair plus pending HIR combination passed both owning
Cargo checks above, with no warnings. `git diff --check` passed. Runtime
multi-parameter behavior, default parity and allocation-failure/drop checks
remain unverified; compilation is not behavioral evidence. The solver-only
checkpoint does not depend on the pending HIR change, and its pre-repair
default/candidate checks also passed against the baseline HIR.

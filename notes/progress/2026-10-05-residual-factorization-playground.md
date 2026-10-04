# Open structural residual factorization playground

Date: 2026-10-05
Status: Bounded characterization; no solver or semantic authority
Governing sources: [scoped constraint solving](../design/2026-10-03-scoped-constraint-solving.md) §§3–5; [open residual factorization](../design/2026-10-03-open-residual-factorization.md) §§1–7; [research playground direction](../design/2026-10-04-inference-research-playgrounds.md)

## Experiment

[`tools/research_residual_factorization.py`](../../tools/research_residual_factorization.py)
compares direct structural satisfaction with normalization into closed
structural checks and retained variable-headed residual inequalities. Its
source fragment has two flexible variables, `Bool`/`Int`, unary and binary
mandatory Records over labels `a,b`, and binary Functions. The assignment
domain contains 15 finite closed types, including empty, one-field, and
two-field Records and Functions with atomic ports.

The checker exhausts all 45 generated endpoint terms on both sides (2,025
inequalities: 1,800 with a variable somewhere in an endpoint and 225 closed-
only) over all 225 `x,y` assignments, doubled by one generic binary symbolic
tag. It records 3,117 comparison visits and 992 retained residual instances.
Every direct solution mask equals the normalized residual mask, including
Function contravariance and mandatory Record width. Each derived comparison
retains the exact same opaque context marker as its original bound; the marker
is bookkeeping only and does not model actual `nu,K,D` or guard semantics.

It then checks 2,048 generated one-to-three-bound packages under supplied
finite `Phi` relations from a fixed family of 128 masks. It conjoins each
`Phi` with the whole package and compares the joint solution and existential
coordinate projections onto `x`, `y`, the generic tag, and `(x,tag)`. Of those
packages, 242 have a nonempty joint solution. This checks that the bounded
residual rewrite composes with a retained correlated predicate; it does not
implement the structural projection operator from the source designs or
construct/solve arbitrary source-generated `Phi/K,D`.

## Deliberate failure and shrink

A mutant that decomposes Function arguments covariantly instead of
contravariantly fails on the minimum two-variable shape found by the search:

```text
Function(x, Bool) <: Function(y, Bool)
x = {}
y = {a: Bool}
```

The direct comparison succeeds because `{a: Bool} <: {}`. The mutant asks for
`{} <: {a: Bool}` and rejects it. This is a checker mutation witness, not a
counterexample to the governing normalization rule.

## Boundary

This experiment covers an acyclic structural grammar and a supplied finite
joint predicate. It does not cover recursive equality/feedback SCCs, rigid
names or scope-guard failures, source generation or proof of stable finite
contexts, effect/Function endpoint semantics, arbitrary `Phi/K,D`, an effective
principal projection, or production acceptance. The broader factorization and
effective-solving obligations remain open exactly as stated in the governing
designs. The finite run is characterization evidence only.

## Review and checks

The script ran with `python3 tools/research_residual_factorization.py`; all
assertions passed with the counts above. `python3 -m py_compile` and
`git diff --check` also passed. One independent `spec_auditor` review found no
structural-rule or equivalence defect. It caught two reporting inaccuracies:
closed endpoint pairs were included in the total, and the opaque context/tag
projections were initially described too strongly. Both were corrected; the
delta review closed with no remaining findings. No Cargo or workspace suite
was run because this is an isolated Python research checker and makes no
compiler changes.

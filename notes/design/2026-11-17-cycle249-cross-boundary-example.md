# Actual propagation adds cross constraints

Show nonvacuity of the reserved-slot two-step example using a constant Common
assignment. Also check why ActivePropagationModels249 retains fresh Compatible
on its input side: first singleton interval0≤1 allows exactEmpty at0 and width
emptyRecord at1, while the second reversed occurrence requires1≤0 and fails.
Thus no second model preserves both public values, although the first model
exists. This is an intended cross-constraint strengthening in the actual
allocation primitives, not a source-language counterexample or new rejection.

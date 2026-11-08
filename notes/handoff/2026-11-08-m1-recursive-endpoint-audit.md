# Recursive interval endpoints: fidelity audit (2026-11-08)

Status: audited against `spec/06-roles.md` 6.5 at `9253f7947`; implementation work follows in additive modules. This is not completion of B4 or B5/B1.

## Initial gate

The recovered `integration/m1-final` checkout at `38e2680ba` passed both required commands before proof changes:

```text
cd lean
lake build --wfail
Build completed successfully (1074 jobs).
lake env lean --trust=0 Audit.lean
Axiom allowlist passed for 78237 declarations from Yulang modules
exit 0
```

The first invocation could not locate the Lake installation. The existing Lean 4.35.0 release was restored to PATH, with the previously documented executor workaround for its own executable path (`/proc/<own-pid>/exe` to `/proc/self/exe`). Neither the Lean kernel nor the trust setting was changed. After that environment repair, both commands above completed with exit status 0.

## Newly confirmed rule

The consistency condition `lower <: upper` and the two merge cross conditions are ordinary subtype constraints. When their endpoints contain invariant nominal arguments, the same centreless interval rule applies recursively inside those arguments. No bound on finite nesting depth is allowed. Every layer still obeys its own declaration's variance, arity, and kind metadata.

## Existing implementation boundary

| Definition | Preserved behavior | Missing connection |
| --- | --- | --- |
| `CommonRoleIntervalGeneration.generate` | Generates every ordered lower/upper cross condition as an ordinary `tyLe` atom. | Its `TyTerm` endpoint grammar has no nominal constructor. |
| `CommonRoleIntervalExpansionChecks.constraints` | Retains each visited goal/capture interval and all original where children. | It emits endpoint checks without recursively solving nominal endpoint comparisons. |
| `CommonDeclaredNominalInspection.inspectArgument` | Reads one declared argument's variance and emits the corresponding value/row comparisons. | A nested nominal argument cannot be re-entered through its existing ordinary term grammar. |
| `CommonRoleIntervalCapture.capture` | Recurses through its explicit finite pair/tick head grammar and retains captured endpoint pairs. | There is no declaration-aware nominal branch. |
| `CommonNominalFullCarrier` | Represents nested nominal and regular forms in the older model. | Its all-invariant nominal interpretation cannot be reused as the current covariant `box` semantics. |

The existing theorems remain valid for their stated carriers. They do not establish the new recursive nominal endpoint obligation. A point argument at every inner node would also miss non-degenerate inner intervals.

## Required additive proof boundary

The new generator must preserve lower and upper endpoints inside invariant children, perform registry checks at every nominal node, and recursively emit all self and cross obligations into the existing ordinary constraint language. Its termination must follow from finite syntax rather than a caller-supplied depth bound. Exactness must be stated against an independent declaration-directed judgment, with every original assignment retained.

This finite recursive endpoint component must remain distinguished from the full regular nominal carrier, general role head capture/deferral, and public `Core.infer` integration. Those larger goals cannot be marked complete merely because the component's build and axiom audit pass.

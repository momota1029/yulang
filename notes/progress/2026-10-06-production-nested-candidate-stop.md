# Production HIR stop for the nested captured-function candidate

Date: 2026-10-06
Baseline: `1a3e6c89c760b36e386ee0033a568613ebc8e524`
Status: frozen, independently regression-audited with no substantive findings; research-only static source-path characterization
Scope: current Yulang3 production lowering/collection for
`my apply f = { my step x = f x; step }`

## Source path

`ParsedFile` retains the complete selected CST snapshot. For this candidate,
the CST represents the outer and local bindings, braced block, local
`f x` application, and final `step` expression. Structural association in
`crates/yu-hir/src/lib.rs` preserves nested `HirExpr::Value` syntax; its
`HirExpr::Apply` is dynamic operator application, not a resolved ordinary-call
node.

Production `lower_module` admits the direct outer binding and installs its
formal `f` as a `HirParameterId`. Lowering then reaches
`crates/yu-hir/src/module.rs::lower_simple_chain`. That path requires a direct
atom and a leaf `HirExpr::Value` with no children. The selected brace body is
not such an atom, so it returns `Unsupported`; `lower_body` records
`UnsupportedExpression` and constructs `ResolvedExpr::Error` under the outer
`ResolvedExpr::Lambda`.

`ResolvedExpr` currently has only `Lambda`, `Integer`, `Name`, and `Error`
variants. The production candidate therefore has no local `step` binding or
`x` formal, no resolved `f`/`x`/`step` uses, and no capture incidence. This is
the current production source-lowering boundary, not a claim that the
Authoritative candidate is invalid.

Constraint collection classifies a Lambda whose body is `Error` as an error
body. `emit_lambda` handles only supported leaves and returns without a
complete Lambda recipe for the unsupported candidate. A total solver result
from such an artifact would not prove source acceptance or infer a typed call
contract.

## Relation to the shadow seam

The default-off shadow projector represents the approved source skeleton and
its new `CaptureUseIncidence` independently of production HIR IDs. The shadow
record links a local Lambda, outer lexical binder, callee-use occurrence and
source position. It does not prove or construct a typed evidence environment,
the original call contract, `beta`/`Slots(beta)`, joint `(nu,K,D)`, provider or
receiver realization. The source-registration and capture-transport gates
remain separate from this production lowering gap.

An old-infer or shadow/F5 type differential for this exact candidate is not
available through the current production call path: production lowering stops
before producing a resolved ordinary call or function capture. This audit did
not alter production acceptance or treat that stop as intended semantics.

## Evidence and limits

This is a static path inspection of the parser/CST association,
`lower_simple_chain`, `ResolvedExpr`, and `ConstraintBatch` collection/emit
branches. No compiler command, test, runtime probe, or production behavior
change was performed. The direct design authority remains the
[nested-block source addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3, which selects the source meaning but explicitly leaves production
acceptance and inference conformance open.

Frozen Oracle was not consulted and supplies no authority. Review, exact-source
execution, solver output, typed application lowering, full source registration,
soundness, principality, source adequacy and production conformance remain
unverified.

An independent regression auditor verified the source-to-HIR-to-collection
path, including the direct-atom stop and the Error-body collection outcome.
The review found no substantive findings. It did not execute the exact source
or certify broader parser/solver behavior.

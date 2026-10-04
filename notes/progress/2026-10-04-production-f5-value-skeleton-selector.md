# Current F5 value-skeleton selector theorem

Date: 2026-10-04
Status: source-generation theorem for a projected structural obligation;
no implementation or semantic authority
Scope: current F5 generation for integer bindings and one-parameter pure
lambda bindings with integer or own-parameter bodies
Depends on: Theorem S in
`2026-10-04-source-generated-callback-structural-theorems.md`, the selector
extension in `2026-10-04-multi-anchor-selector-witness.md`, and current
`yu-hir` / `yu-solver` generation clauses

## Statement

For every finite, error-free current HIR module consisting only of integer
bindings and one-parameter lambdas with an integer-literal body or the
lambda's own parameter as body, the **pre-generalization value-skeleton
projection** of the source facts admitted by current F5 satisfies Theorem S's
grounded / one-open-anchor condition after finite rational equality
normalization. Therefore, if this projected structural package is
satisfiable, it has a regular witness.

The projection uses existing `ComponentKind::Value` endpoints, the value
children of the existing positive Function term, and original value bounds.
It omits Function effect children only to state a theorem about this
projection. It does not claim equivalence with full F5, decide a coupled
Function/effect inequality, or derive the denotation of either effect port.
In particular, the result cannot be used to accept a source module whose full
coupled package is unsatisfiable.

## Source-generated package

Inspect the finite HIR before solving and select exactly the stated source
forms. Collection records definition and literal endpoints plus parameter
recipes; session construction allocates the live parameter value endpoints
used by Function children. The existing source rules give these projected
clauses:

| HIR form | Value-skeleton constraints |
|---|---|
| integer binding | `Int <: v`, `v <: Int`, and `v <: root` |
| lambda `f x = x` | `Function(x,x) <: root` |
| lambda `f x = 1` | `Function(x,v) <: root`, with `Int <: v` and `v <: Int` |

For the identity, the negative Function argument and positive result refer to
the same live parameter ordinal. For the integer-returning lambda, `v` is the
integer body's value endpoint; the parameter remains a free endpoint. Each
definition has exactly one root fact, and the chosen grammar emits no
resolved module-name uses, rigid names, or Record descriptors. Integer
bindings do have a free/free edge `v <: root`; its component is grounded by
the closed `Int` endpoints.

At source level the inventory is finite and checkable without solving: visit
each HIR item once, reject the module if it falls outside the grammar, and
check that each lambda body's name resolution points to its own parameter.
The generation mapping is confirmed by `emit_integer`, `emit_lambda`, and
`admit_lambda_fact` in `crates/yu-solver/src/lib.rs`; the identity and
constant-body source cases also have existing focused assertions there.

## Selector proof

After rational equality normalization, the integer occurrence and definition
root lie in one free/free component. Its only descriptor anchors are the
closed `Int` endpoints, so it is grounded. The root of a lambda has exactly
one nonfree value endpoint in an original bound:
its positive `Function` descriptor. This descriptor is open because it
reaches the parameter endpoint (and, for identity, the same endpoint again
as the result). No second descriptor root is incident to that free component.
The integer body contributes only its closed `Int` bounds to its own endpoint
component. Each lambda parameter is an isolated free component: Function
child references are constructor edges, not incident free/free bounds, so it
has no descriptor anchors and satisfies Theorem S's no-anchor `G` case
vacuously. All rigid-permission obligations are vacuous.

Thus every free component is either grounded by closed endpoints or has one
open Function anchor. This is precisely Theorem S's checked incidence
condition. The source-generation theorem above proves the premise by
enumerating HIR and generated value facts; Theorem S then gives the regular
witness whenever this projection is satisfiable. This is not the selector
theorem's conclusion assumed as a premise and does not ask whether an unknown
regular solution exists.

## Boundary with the full generated constraints

`admit_lambda_fact` records the actual positive four-port Function fact and
the `ConstraintStore` retains the result-effect occurrence and its polarized
bounds. Current `constrain_live` processes the value argument/result children
and effect argument/result children as one stored Function-pair expansion.
The projection above does not replace that package with four independent
subtyping judgments: it proves only a regular-witness property of its
existing value skeleton.

Theorem S excludes `K,D`, effect rows, casts/adapters, and joint profile
evidence. So this result does not establish full F5 satisfiability, callback
adequacy, scheme principality, or successor inference correctness. It is a
strictly stronger source bridge than the equation-only structural shadow for
this HIR grammar: it includes the actual generated value-side Function head
bound. The exact lift from this projection to the coupled four-port source
interface remains open.

No compiler code or tests changed or ran. The result adds no source rule,
solver carrier, or implementation authority.

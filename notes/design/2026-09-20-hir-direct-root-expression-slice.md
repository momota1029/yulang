# HIR direct-root expression slice

Status: Authoritative; construction complete (2026-09-20)

Approved by: user, 2026-09-20.

## Supersession

This record supersedes the 2026-09-19 simple-module slice only for the
`HirItem = Binding | Error` product and direct-root `OperatorChain` treatment
as `UnsupportedItem`. Binding admission, the binding-only namespace, `DefId`,
error ordering, availability, and recovery contracts remain unchanged.

## Scope

Extend the completed simple-module HIR slice with direct-root `OperatorChain`
items. This is a neutral HIR ownership correction before expression identity
and type-constraint collection.

## Decision

`HirItem` gains `Expression(ResolvedExpr)`. Every direct-root
`OperatorChain` is planned and lowered in source order through the same
already-supported simple atom lowering used for binding bodies:

- integer atoms lower to `ResolvedExpr::Integer`;
- identifier atoms resolve against the completed module namespace, including
  forward references;
- unresolved or ambiguous identifiers produce one existing lowering error at
  the identifier range, attached to `DirectRootItem(ordinal)`;
- recovery-free unsupported complex chains lower to `ResolvedExpr::Error` with
  one `UnsupportedExpression` attached to `DirectRootItem(ordinal)`;
- recovery-bearing chains retain only CST-derived causes attached to
  `DirectRootItem(ordinal)`: they neither resolve retry operands nor add
  `UnsupportedExpression`.

An operator-definition body that is a sibling root `OperatorChain` follows the
same rule and becomes `Expression`; its `OperatorHeader` remains independently
unsupported. Root expressions never enter the binding namespace or consume a
`DefId` ordinal.

For the existing `startup_minimal` fixture, `42` yields one expression item
with spelling and range `0..2`, and no errors or diagnostics.

## Deferrals

This slice introduces no `ExprId`, type, constraint, solver, evaluation order,
program-result marker, runtime behavior, syntax/CST change, or backend work.
It does not infer that a final root expression is executable output.

## Invariants and proof

Binding planning, stable `DefId`, binding-body association, source order,
recovery preflight, and CST-derived cause attachment remain unchanged. Root
expressions use no source/token heuristic beyond their existing CST node. Tests
cover the exact fixture, mixed source order, forward/backward name resolution,
unresolved/ambiguous names, unsupported/recovery paths, and deterministic
lowering. Roll back if root expressions require evaluation semantics or source
heuristics to be represented honestly.

## Construction and verification

The root planner now distinguishes direct expressions without changing
binding-only namespace/`DefId` planning. Focused direct-root tests and the full
`yu-hir` suite pass; syntax test compilation remains warning-free.

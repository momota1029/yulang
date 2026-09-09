# Assignment tail

## 1. Scope

Assignment is a terminal outer continuation in an `OperatorChain`.
It accepts one-character `=` and exactly one right-hand side.
This page defines only the surface spelling, CST, and recovery.

Assignment is outer-only.
It requires an enabled continuation outside an ML argument.
A candidate in a lower binding-threshold context or an ML argument is rejected without consuming source or emitting CST or recovery output.

The right-hand side is either an inline `Expression` or an indented `Statement` block.
It is not a comma-owning inline list.

## 2. Accepted spelling

The following are inline assignment forms.

```text
x = y
x=-y
```

Assignment is judged after an admitted dynamic LED operator.
Therefore, `x == y` remains a dynamic infix rather than an assignment followed by `=`.

## 3. Flat source-order CST

`AssignmentTail` neither owns nor wraps a left operand.
The open `OperatorChain` appends `AssignmentTail` after the completed left expression's source-order children.
In the Rowan CST, an `AssignmentTail` node is placed within the flat `OperatorChain`.

```text
OperatorChain :=
    <left-expression children in source order>
    AssignmentTail

AssignmentTail :=
    "=" G* Expression
  | "=" <existing indented Statement block>
```

Trivia before a committed `=` remains a direct child of `OperatorChain`.
`AssignmentTail` owns `=`, accepted leading trivia after it, and the right-hand side in source order.

When the newline introduces indentation strictly deeper than the introduction position, the right-hand side is the existing indented `Statement` block.
Otherwise, `AssignmentTail` requires exactly one inline `Expression`.

## 4. Termination

After a successful right-hand side, `AssignmentTail` closes.
It returns that exit to its enclosing owner and does not scan another outer-chain continuation.

This rule applies only to assignment.
The `as Type` annotation is a separate tail, and this page does not define its syntax.

## 5. Recovery

Before an inline right-hand side, a fence, abstract boundary, active stop, line stop, separator, close, non-NUD bracket opener, non-continuing layout, or EOF emits one zero-width `Missing` in `AssignmentTail`'s RHS slot.
At ordinary EOF, `AssignmentTail` may first emit leading trivia that it owns and anchors the `Missing` at physical EOF.
At a protected boundary, the whole protected item and its unowned leading trivia remain pending.

When non-boundary non-NUD material starts the right-hand side, its initial leading trivia remains outside `Error`.
Assignment consumes one maximal lexical run as `Error`.
Internal leading trivia belongs to the malformed `Error` run; leading trivia before a retry or protected boundary remains outside it.
If an admitted right-hand side follows, it retries the same single RHS slot.
If the run reaches a protected boundary, it returns the `Error` and adds no `Missing`.

Nested `Expression` recovery retains its existing roles.
This tail does not reclassify it.

The `Missing` and `Error` notation on this page follows the [Rowan CST notation](../conventions/rowan-cst.md).
The site-wide conventions define current-versus-approved `Error` / `Invalid` rendering.
This page does not claim that the pending topology migration is implemented.

## 6. Exclusions

This construct does not define canonical AST materialization, HIR association, operator-table changes, or declaration-equality scanning.
`AssignmentTail` is a flat CST form and has no semantic target.

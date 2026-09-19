# Assignment tail

## 1. Authority and scope

This page defines the terminal `AssignmentTail` in `syntax-v0`.
The `Assignment` section of the 2026-09-09 expression-assignment-tail design defines assignment role, admission, and tail topology.
The direct inline RHS slot follows the Authoritative error-admission schema slice from that date.
The 2026-09-08 indented-Statement role transport governs only shared block recovery for an indented RHS.

The page covers `=`, direct inline RHS, an `IndentedStatementBlock` RHS on a deeper introduced line, and their direct CST and recovery.
It does not define assignment evaluation, left-operand interpretation, operator association, HIR, or types.

## 2. Accepted syntax

```text
AssignmentTail := "=" AssignmentRhs
AssignmentRhs := OperatorChain | IndentedStatementBlock
```

Only an outermost, enabled, non-ML continuation admits assignment.
After an admitted dynamic LED operator declines, the tail acquires exactly one `=`.
A strictly deeper introduced line selects `IndentedStatementBlock`.
Otherwise the tail selects one inline `OperatorChain`.
The inline RHS is not a comma-owning list.

## 3. Admission and boundaries

A candidate at a lower threshold or in an ML argument remains pending and creates neither `AssignmentTail` nor recovery.
In `x=-y`, `-y` is the inline RHS.
In `x==y`, dynamic LED admission has priority, so no assignment tail is created.

After a successful RHS, the tail closes and does not scan another outer continuation.
An active stop, separator, close, non-NUD bracket opener, non-continuing layout, fence boundary, or EOF can leave the inline slot without an RHS.
The protected item and its unowned leading remain pending.

## 4. Direct Rowan CST

`AssignmentTail` neither owns nor wraps the left expression.
The enclosing `OperatorChain` owns the left children and trivia before `=`, then places one `AssignmentTail`.

```text
OperatorChain := <left-expression children and pre-`=` trivia> AssignmentTail
AssignmentTail := Equals (OperatorChain | IndentedStatementBlock)
```

For the direct inline alternative, `AssignmentTail` contains `Equals`, native leading trivia, and one RHS `OperatorChain` in source order.
There is no `InlineRhs` node.
For the indented alternative, `AssignmentTail` contains `IndentedStatementBlock` as a direct child after `Equals`.

## 5. Recovery CST

When the inline RHS is absent, `AssignmentTail` places one zero-width `Missing` in the `Assignment(Rhs)` slot.
At ordinary EOF, the tail can first place leading that it owns.
At a protected boundary, the boundary item and unowned leading are not `AssignmentTail` children.

A non-boundary, non-NUD inline run is a maximal raw `Error` group directly under `AssignmentTail`.
Initial rejected-item leading remains outside the group.
Interior leading belongs to the group.
Retry leading belongs to the new RHS `OperatorChain`.
An admitted retry fills the same RHS slot.
When the group reaches a protected boundary, it leaves that boundary in place and adds no same-cause `Missing`.

For the indented alternative, block-entry and child Statement `Missing` or raw `Error` belong to `IndentedStatementBlock`, which transports the `Assignment(IndentedStatement)` role.
An inline raw group is not wrapped in `Invalid`.

## 6. Source/CST examples

`x = y` has a direct inline RHS.

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="x" /></IdentifierExpression>
  <Whitespace text=" " />
  <AssignmentTail>
    <Equals text="=" />
    <Whitespace text=" " />
    <OperatorChain><IdentifierExpression><Identifier text="y" /></IdentifierExpression></OperatorChain>
  </AssignmentTail>
</OperatorChain>
```

In `x = @ y`, the chain after the raw group fills the same inline RHS slot.

```xml
<AssignmentTail>
  <Equals text="=" />
  <Whitespace text=" " />
  <Error text="@" />
  <OperatorChain><IdentifierExpression><Whitespace text=" " /><Identifier text="y" /></IdentifierExpression></OperatorChain>
</AssignmentTail>
```

The following source selects the indented alternative.

```text
x =
  y
```

Its `AssignmentTail` has `Equals` followed by one direct `IndentedStatementBlock` child.
The shared block construct owns its ordered contents.

## 7. Composition

`AssignmentTail` is a terminal continuation of a [dynamic operator chain](operator-chain.md).
An inline RHS uses the ordinary operand and tail rules of that chain.
An indented RHS delegates to the shared `IndentedStatementBlock` and does not move nested Statement recovery into the assignment tail.

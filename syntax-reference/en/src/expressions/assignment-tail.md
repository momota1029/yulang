# Assignment tail

## 1. Scope and admission

This page specifies the direct inline `Assignment(Rhs)` slot of
`AssignmentTail`. It defines the source-order Rowan CST, recovery shape, and
later diagnostic projection for that slot.

The examples use the site-wide [Rowan CST notation](../conventions/rowan-cst.md),
including its reversible `text`-attribute escaping rules.

Assignment is a terminal outer continuation in an `OperatorChain`. It acquires
one `=` after an admitted dynamic LED operator has declined. The continuation
must be enabled, outermost, and outside an ML argument. A lower-threshold or
ML candidate leaves its source pending and emits neither an `AssignmentTail`
nor recovery elements. Thus `x=-y` is an assignment with a prefix RHS, while
`x==y` remains a dynamic infix expression.

The direct inline slot requires one RHS. It is not a comma-owning inline list.
After an admitted RHS, `AssignmentTail` closes and does not scan another outer
continuation.

## 2. Source-order CST

`AssignmentTail` neither owns nor wraps the left expression. The enclosing
`OperatorChain` owns the left-expression children and the trivia before `=`.
It then appends one `AssignmentTail` node.

The direct inline child alternatives are shown below. This grammar omits
trivia only in the alternatives; the following sections place it explicitly.

```text
OperatorChain := <left-expression children and pre-`=` trivia> AssignmentTail
AssignmentTail := Equals (Missing | Error+ | Error+ OperatorChain | OperatorChain)
Equals := "="
```

For an accepted inline RHS, `AssignmentTail` contains its `Equals` token,
then its native leading trivia, then one concrete RHS `OperatorChain`. There
is no `InlineRhs` node.

```xml
<AssignmentTail>
  <Equals text="=" />
  <Whitespace text=" " />
  <OperatorChain>
    <IdentifierExpression>
      <Identifier text="y" />
    </IdentifierExpression>
  </OperatorChain>
</AssignmentTail>
```

Initial leading before an accepted or initially rejected direct RHS is native
trivia directly under `AssignmentTail`. It precedes that RHS `OperatorChain`
or the direct `Error` tokens. Leading at an admitted retry is native trivia in
the new RHS `OperatorChain`; it is not part of the preceding raw group.

## 3. Absent and raw RHS forms

At an admitted stop, boundary, separator, close, non-NUD bracket opener,
non-continuing layout, or EOF, the required inline RHS is absent. The tail
contains one zero-width `Missing` in its `Assignment(Rhs)` slot.

```xml
<AssignmentTail>
  <Equals text="=" />
  <Whitespace text=" " />
  <Missing />
</AssignmentTail>
```

At ordinary EOF, `AssignmentTail` may first emit leading trivia that it owns.
The `Missing` range is then the physical EOF. At a protected boundary, the
complete boundary item and its unowned leading remain pending. They do not
become `AssignmentTail` children.

If a non-boundary, non-NUD run begins the RHS, the tail emits one maximal raw
group as adjacent direct `Error` tokens. Initial rejected-item leading stays
outside the group. Interior leading belongs to the group. A terminal group
returns a protected boundary unchanged and does not add a same-cause
`Missing`.

```xml
<AssignmentTail>
  <Equals text="=" />
  <Whitespace text=" " />
  <Error text="@" />
  <Error text="  " />
  <Error text="@" />
</AssignmentTail>
```

If an inline expression is admitted after the raw group, it fills the same
RHS slot. The retry-leading whitespace belongs to the new RHS child.

```xml
<AssignmentTail>
  <Equals text="=" />
  <Whitespace text=" " />
  <Error text="@" />
  <OperatorChain>
    <IdentifierExpression>
      <Whitespace text=" " />
      <Identifier text="y" />
    </IdentifierExpression>
  </OperatorChain>
</AssignmentTail>
```

The raw group has no `Invalid` wrapper. `Error` is a token leaf, and its
adjacent leaves describe physical fragments rather than an invented grammar.

## 4. Slot projection and nested ownership

For this direct inline slot, a `Missing` node and one maximal raw `Error`
group each project `Assignment(Rhs)`, whose expected syntax is `Expression`
and whose primary expectation index is zero. A `Missing` projects at its
zero-width CST range. A raw group projects once over the combined range of
its adjacent `Error` tokens. It is not a second `Missing` or an unexpected
payload.

Nested recovery belongs to the nested grammar slot. For example, a `Missing`
inside a `FieldTail` in the RHS `OperatorChain` does not become an
`Assignment(Rhs)` recovery occurrence.

CST-derived diagnostic publication is pending. It will use the node range and
the maximal direct `Error` group described here. The
[source-root and diagnostic ownership](../conventions/source-root-and-diagnostics.md)
convention defines that publication boundary.

## 5. Exclusions

An RHS on a deeper introduced line delegates to `IndentedStatementBlock`.
Its block entry, child slots, recovery, and diagnostic projection are not
specified on this page.

This page does not define an AST, HIR association, operator-table changes, a
complete slot inventory, or the later public diagnostic result.

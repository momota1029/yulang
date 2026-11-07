# List expressions

## 1. Authority and scope

This page defines `ListExpression` in `syntax-v0`.
Its accepted syntax and direct Rowan CST follow WP-7 of the Authoritative parser gap closure addendum dated 2026-11-04.
The [layout-aware comma-or-newline-delimited sequence authority](../cross-cutting/layout-aware-separator-authority.md) governs this construct's separator rule.
See the [syntax content model](../conventions/syntax-content-model.md), [Rowan CST notation](../conventions/rowan-cst.md), and [recovery `Error` and `Invalid` topology](../conventions/recovery-error-invalid-topology.md) for shared notation and recovery elements.

The page covers brackets, ordinary items, spread items, comma and layout separators, closes, and recovery in those slots.
It does not define list value types, spread evaluation, element typing, or list patterns.

## 2. Accepted syntax

```text
ListExpression :=
    "[" G*
    [
        ListExpressionItem
        { ListExpressionSeparator ListExpressionItem }
        [ ListExpressionSeparator ]
    ]
    "]"

ListExpressionItem := OperatorChain | ListExpressionSpreadItem
ListExpressionSpreadItem := ".." G* OperatorChain
ListExpressionSeparator := "," G* | qualifying newline
```

Accepted forms include `[]`, `[1]`, `[1, 2,]`, and `[1, ..xs, 3]`.
Zero or more spread items may occur in any item position.
Each ordinary item and spread RHS is an `OperatorChain` read with `MlMode::All`.
Therefore `[1 2]` has no missing separator: it contains one item, the ML application `1 2`.

## 3. Admission and boundaries

`[` starts a `ListExpression` in value position.
When `[` follows an existing operand with no trivia, it starts an `IndexTail`, so `xs[0]` is an index.
When `[` has leading trivia, it can start an ML argument, so `xs [0]` is an application whose argument is the list expression `[0]`.

After an item's `OperatorChain` has consumed its ML applications and fixed tails, the list owner recognizes a comma, the matching `]`, or a qualifying current-depth newline as a boundary.
A deeper newline remains in the current item as continuation trivia.
If the item parser returns a same-line next-item candidate, the list owner places `Missing` in the separator slot and retries the item at the same position.

## 4. Direct Rowan CST

`ListExpression` is a direct child of `OperatorChain`.
Its children occur in source order as `LBracket`, ordinary-item `OperatorChain` nodes, `ListExpressionSpreadItem` nodes, literal commas, trivia, and `RBracket`.
A qualifying newline remains trivia and does not create a synthetic separator node.

Each `ListExpressionSpreadItem` contains `DotDot` and its RHS `OperatorChain`.
An ordinary item has no additional item wrapper.

## 5. Recovery CST

When the initial item slot or an item slot after a comma lacks its required element, `ListExpression` places a zero-width `Missing` in that slot.
A missing local close places `Missing` in the close slot and leaves a protected outer boundary unconsumed.
Thus unclosed `[1, 2` has a missing close at the end of the source, while `[,]` has a missing item before the comma.

The spread marker belongs to `ListExpressionSpreadItem` even when its RHS is absent.
In `[..]`, the spread node has a zero-width `Missing` after `DotDot`, while the real `RBracket` remains owned by the list.

An ordinary malformed item run is a raw `Error` group directly under `ListExpression`.
A foreign close consumed by this owner is a raw `Error` group in `ExpressionDelimitedForeignClose`.
For example, in `[1)]`, `)` is foreign-close recovery and the following `]` remains the list close.

## 6. Source and CST examples

`[1 2]` has one item containing an ML application.

```xml
<OperatorChain>
  <ListExpression>
    <LBracket text="[" />
    <OperatorChain>
      <IntegerLiteral><Integer text="1" /></IntegerLiteral>
      <Whitespace text=" " />
      <MlArgument><OperatorChain><IntegerLiteral><Integer text="2" /></IntegerLiteral></OperatorChain></MlArgument>
    </OperatorChain>
    <RBracket text="]" />
  </ListExpression>
</OperatorChain>
```

`[..]` recovers its RHS while retaining the spread owner.

```xml
<OperatorChain>
  <ListExpression>
    <LBracket text="[" />
    <ListExpressionSpreadItem>
      <DotDot text=".." />
      <Missing />
    </ListExpressionSpreadItem>
    <RBracket text="]" />
  </ListExpression>
</OperatorChain>
```

## 7. Composition

[Dynamic operator chains](operator-chain.md) define an inner chain's operator roles, ML applications, and fixed tails.
The outer chain owns continuations after the list expression.
The corresponding pattern form is defined by [list patterns](../patterns/list-pattern.md).

For declaration-line recovery at an unmatched opener, see [unmatched delimiters](../conventions/recovery-error-invalid-topology.md#unmatched-delimiters).

# `with:` body tail

## 1. Authority and scope

This page defines the terminal `WithBodyTail` in `syntax-v0`.
The 2026-08-20 `yu-syntax` architecture defines its accepted grammar and direct Rowan CST.
The Authoritative 2026-09-08 Colon/With inline and indented-Statement role-transport records define its recovery and indented-body transport.
See the [syntax content model](../conventions/syntax-content-model.md), [Rowan CST notation](../conventions/rowan-cst.md), and [recovery `Error` and `Invalid` topology](../conventions/recovery-error-invalid-topology.md) for shared notation.

The page covers a generic-expression `with:` continuation, its one inline canonical `Statement` or indented statement block, and their recovery CST.
It does not define declaration companions, `with { ... }`, target association, companion semantics, HIR, types, diagnostics wording, or formatting.

## 2. Accepted syntax

```text
WithBodyTail := WithKw G* ":" WithBody
WithBody := InlineWithBody | IndentedStatementBlock
InlineWithBody := Statement [ ";" ]
```

`with` is an exact maximal word, so `withx` and `with?` do not admit this tail.
The required colon is a lone colon; `::` is not split.
Trivia between `with` and `:` may include a newline.
A physical newline after the colon selects an indented block only at strictly deeper indentation.
Otherwise the body is one inline canonical `Statement`.

## 3. Admission and boundaries

At an operand-complete position, active owner stops, matching closes, and equal-or-shallower newlines return before this tail.
When `with` is not stopped, its exact probe takes priority over dynamic LED, fixed postfix, ML application, and colon application.
Accepting it commits the tail: it cannot fall back to an identifier, operator, or ML argument.

`WithBodyTail` is terminal and has no target child.
Its body starts a fresh statement and chain context.
Thus the nested tail in `a with: b: c` or `a with: b with: c` belongs to the body, not to the outer `a` chain.
The optional inline semicolon is owned once by the tail; later trivia and outer boundaries remain outside it.

## 4. Direct Rowan CST

`WithBodyTail` is a direct terminal child of `OperatorChain` and does not wrap its target.
It contains `WithKw`, introducer trivia, `Colon`, body trivia, and either one direct `Statement` or one direct `IndentedStatementBlock` in source order.
There is no `InlineWithBody` CST wrapper.

```text
OperatorChain := <completed-chain children> WithBodyTail
WithBodyTail := WithKw G* Colon (Statement [ Semicolon ] | IndentedStatementBlock)
```

An inline body's `Statement` owns its nested `OperatorChain` and any nested terminal tail.
An indented body owns its statement separators through `IndentedStatementBlock`; `WithBodyTail` does not own a semicolon after that alternative.

## 5. Recovery CST

An accepted `with` without its colon places one zero-width `Missing` in `WithBody(Introducer)` and does not cascade a body missing node at the same boundary.
When an inline statement starts where the colon is missing, it retries that same position as the body after the introducer missing node.
`::` remains available to body or outer recovery after that missing node.

An accepted colon with no body places one zero-width `Missing` in `WithBody(Body)`.
At an equal-or-shallower newline, the newline and following item remain with the outer statement owner.
A malformed non-statement inline run is one maximal non-empty raw `Error` group in `WithBody(Body)`, followed by same-slot retry at an admitted canonical statement.
Nested recovery belongs to the nested statement or tail and is not duplicated by `WithBodyTail`.

The indented alternative transports `WithBody(IndentedStatement)` to the shared block entry and child-statement recovery slots.
All protected commas, closes, dedents, stops, and retry points remain unconsumed boundaries.

## 6. Source/CST examples

`a + b with: cleanup` places the body after the completed outer chain.

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="a" /></IdentifierExpression>
  <Whitespace text=" " />
  <InfixOperatorUse><Operator text="+" /></InfixOperatorUse>
  <Whitespace text=" " />
  <IdentifierExpression><Identifier text="b" /></IdentifierExpression>
  <Whitespace text=" " />
  <WithBodyTail>
    <WithKw text="with" /><Colon text=":" /><Whitespace text=" " />
    <Statement><OperatorChain><IdentifierExpression><Identifier text="cleanup" /></IdentifierExpression></OperatorChain></Statement>
  </WithBodyTail>
</OperatorChain>
```

In `a with: b: c`, the nested colon is in the body's chain.

```xml
<WithBodyTail>
  <WithKw text="with" /><Colon text=":" /><Whitespace text=" " />
  <Statement>
    <OperatorChain>
      <IdentifierExpression><Identifier text="b" /></IdentifierExpression>
      <ColonApplicationTail><Colon text=":" /><Whitespace text=" " /><OperatorChain><IdentifierExpression><Identifier text="c" /></IdentifierExpression></OperatorChain></ColonApplicationTail>
    </OperatorChain>
  </Statement>
</WithBodyTail>
```

The following source contains one direct `IndentedStatementBlock` body.

```text
value with:
  body
```

## 7. Composition

[Dynamic operator chains](operator-chain.md) define the terminal continuation position and sibling tails.
[Colon application](colon-application.md) may occur inside the body statement.
The shared indented block owns an indented body's sequence and transports `WithBody(IndentedStatement)` recovery.

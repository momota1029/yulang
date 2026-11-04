# Lambda expressions

## 1. Authority and scope

This page defines `LambdaExpression` in `syntax-v0`.
Its accepted syntax, admission, and direct Rowan CST follow WP-10 of the Authoritative parser gap closure addendum dated 2026-11-04.
See [dynamic operator chains](operator-chain.md) for the body's operator and application rules.
See the [syntax content model](../conventions/syntax-content-model.md), [Rowan CST notation](../conventions/rowan-cst.md), and [recovery `Error` and `Invalid` topology](../conventions/recovery-error-invalid-topology.md) for shared notation and recovery elements.

The page covers the backslash, parameter sequence, exact arrow, body, whole-header admission, and recovery within parameter patterns.
It does not define currying semantics, binding, capture, wildcard meaning, or typing.

## 2. Accepted syntax

```text
LambdaExpression := "\\" LambdaHeaderGap LambdaParameter
                    { LambdaHeaderGap LambdaParameter }
                    LambdaHeaderGap ExactArrow OperatorChain

LambdaParameter := Identifier | ParenthesizedPattern
ExactArrow := "->"
```

`LambdaHeaderGap` is empty or existing inline trivia with no logical layout newline.
At least one parameter is required, and a bare parameter must be an identifier.
Any other pattern must be enclosed in parentheses.

```yulang
\x -> x + 1
\x y -> x + y
\(a, b) -> a
\x (just y) -> y
\(x: int) -> x
```

Currying multiple parameters is a semantic rule and does not rewrite the CST into nested lambdas.
Only an explicitly nested source form such as `\x -> \y -> x` has another `LambdaExpression` in its body.

## 3. Admission and boundaries

In value position, the parser examines the whole header from source before dynamic operator selection.
It commits to a lambda only when the backslash, one or more admitted parameters, and the exact `->` are all present.
Lookahead for a parenthesized parameter balances parentheses and ignores parentheses inside nested parentheses, literals, line comments, and nested block comments.
The lookahead does not recursively run the parser or create CST and diagnostics.

If the header has no arrow, has unbalanced parentheses, or contains a parameter outside the admitted forms, the backslash does not become a lambda token.
For example, `\x y`, `\(a, b -> a`, `\1 -> x`, `\x.y -> x`, and `\x ->> x` are not lambdas.
Ordinary operator selection and recovery then start at the same position, so a declared `\` operator remains available.
A complete header takes precedence over an operator with the same spelling.

Parameter adjacency follows the existing Pattern rules.
In the complete header `\(a, b)(c) -> a`, the adjacent `(c)` is a `PatternCallTail` of the preceding pattern.
The header therefore has one parenthesized-pattern parameter, not two.

A lambda is admitted both at expression NUD sites and where leading trivia can start an ML argument.
Thus both `f (\x y -> x)` and `f \x y -> x` are accepted.
The body is an `OperatorChain` read with `MlMode::All`; it does not cross a caller comma, close, qualifying newline, or fence.

## 4. Direct Rowan CST

`LambdaExpression` is a direct child of `OperatorChain`.
Its children occur in source order as `Backslash`, the parameters, `Arrow`, and the body's `OperatorChain`.
Trivia remains in the same source order.

A bare identifier parameter is a direct `Identifier` token with no `Pattern` wrapper.
A parenthesized parameter is a direct `Pattern` node containing `ParenthesizedPattern`.
There is no extra parameter-sequence wrapper and no synthetic lambda for currying.

```xml
<LambdaExpression>
  <Backslash text="\\" />
  <Identifier text="x" />
  <Whitespace text=" " />
  <Pattern>
    <ParenthesizedPattern>
      <LParen text="(" />
      <Pattern>...</Pattern>
      <RParen text=")" />
    </ParenthesizedPattern>
  </Pattern>
  <Whitespace text=" " />
  <Arrow text="->" />
  <OperatorChain>...</OperatorChain>
</LambdaExpression>
```

## 5. Recovery CST

After a complete header commits, the ordinary Pattern parser reads each parenthesized parameter.
Its local comma, missing-item, foreign-close, and type-annotation recovery therefore follow the [pattern forms](../patterns/pattern-core.md).
For example, the trailing comma in `\(a,) -> a` is accepted, while `\(,) x -> x` has `Missing` inside its parameter `Pattern`.

The bodyless form `\x ->` has a complete header.
It retains `Backslash`, the parameter, and `Arrow`, then places a zero-width `Missing` in the body's mandatory operand slot.
In contrast, an input that fails header admission creates no `LambdaExpression` and starts no lambda-specific recovery.

## 6. Composition

[Patterns](../patterns/index.md) define syntax and recovery within a parameter.
[Dynamic operator chains](operator-chain.md) define operators, ML applications, and fixed tails in the body and after the lambda.


# Parenthesized expressions

## 1. Authority and scope

This page defines `ParenthesizedExpression` in `syntax-v0`.
Its accepted syntax and direct Rowan CST follow the parenthesized-expression and precedence-neutral-chain sections of the 2026-08-20 `yu-syntax` architecture, together with the 2026-09-08 expression-delimited current-Item recovery and the 2026-09-10 raw-slot CST amendment.
The [layout-aware comma-or-newline-delimited sequence authority](../cross-cutting/layout-aware-separator-authority.md) governs this construct's separator rule and supersedes the earlier parenthesized separator portions only in that scope.
See the [syntax content model](../conventions/syntax-content-model.md), [Rowan CST notation](../conventions/rowan-cst.md), and [recovery `Error` and `Invalid` topology](../conventions/recovery-error-invalid-topology.md) for the syntax-v0 freeze, shared notation, and recovery elements.

The page covers parentheses, `OperatorChain` elements, comma and layout separators, closes, and recovery in those slots.
It does not define unit, grouping, or tuple interpretation; operator association; type inference; runtime representation; or other parenthesized grammars.

## 2. Accepted syntax

```text
ParenthesizedExpression :=
    "(" G*
    [
        OperatorChain
        { ParenthesizedSeparator OperatorChain }
        [ ParenthesizedSeparator ]
    ]
    ")"

ParenthesizedSeparator := "," G* | qualifying newline
```

The accepted forms include `()`, `(a)`, `(a,)`, and lists with more than one element.
A comma is a literal separator.
A qualifying current-depth newline is an element boundary when its following indent is equal to or shallower than the base indentation taken from opening trivia.
A newline with a deeper indent remains in the current `OperatorChain` as continuation trivia.
A semicolon is not a separator in this construct.

## 3. Admission and boundaries

`(` is admitted in value position.
Each element is an `OperatorChain` that stops at a comma, `)`, or qualifying current-depth layout newline of the current parentheses.
A deeper newline remains continuation trivia in the current element.
A completed parenthesized expression returns to its outer `OperatorChain`, which can continue with a fixed postfix, suffix, or infix use.

A same-line next-element candidate with no separator recovers the separator slot and retries the element at the same position.
Caller-owned boundaries and nested delimiter scopes remain unconsumed by this construct.
The local owner retains comma and matching `)` ownership, and admits matching `)` first as the local close.

## 4. Direct Rowan CST

`ParenthesizedExpression` is a direct child of `OperatorChain`.
Its children occur in source order as `LParen`, zero or more `OperatorChain` elements, literal commas, trivia, and `RParen`.
A newline separator remains trivia; it does not create a synthetic separator node.
The comma in `(a,)` remains a source-bearing leaf.

Each inner `OperatorChain` is a separate element.
The parenthesized node does not wrap elements in grouping or tuple nodes.

## 5. Recovery CST

When the initial item slot or an item slot after a comma lacks its required element, `ParenthesizedExpression` places one zero-width `Missing` in that slot.
An immediate real `)` is the empty form and has no element `Missing`.
An element retry without a separator places `Missing` in the separator slot.
A missing local close places `Missing` in the close slot and leaves a protected outer boundary unconsumed.

An ordinary malformed item run is an adjacent raw `Error` group directly under `ParenthesizedExpression`.
A rejected semicolon is a raw `Error` group in `ExpressionDelimitedSeparator`.
A foreign close consumed by this owner is a raw `Error` group in `ExpressionDelimitedForeignClose`.
Each wrapper contains one nonempty group only and contains no `Missing`, accepted punctuation, retry leading, or `Invalid`.

If an element is admitted after a raw group, it fills the same item slot.
A group that reaches a protected boundary leaves that boundary in place and adds no same-cause `Missing`.

## 6. Source/CST examples

`()` has no elements.

```xml
<OperatorChain>
  <ParenthesizedExpression>
    <LParen text="(" />
    <RParen text=")" />
  </ParenthesizedExpression>
</OperatorChain>
```

`(a,)` has one element and a literal comma.

```xml
<OperatorChain>
  <ParenthesizedExpression>
    <LParen text="(" />
    <OperatorChain><IdentifierExpression><Identifier text="a" /></IdentifierExpression></OperatorChain>
    <Comma text="," />
    <RParen text=")" />
  </ParenthesizedExpression>
</OperatorChain>
```

In `(;)`, the semicolon marks the separator-recovery slot.

```xml
<OperatorChain>
  <ParenthesizedExpression>
    <LParen text="(" />
    <ExpressionDelimitedSeparator><Error text=";" /></ExpressionDelimitedSeparator>
    <RParen text=")" />
  </ParenthesizedExpression>
</OperatorChain>
```

## 7. Composition

[Dynamic operator chains](operator-chain.md) define the operator roles and fixed tails of an inner chain.
The outer chain owns continuations after the parenthesized expression.
The shared recovery topology defines the diagnostic interpretation of direct `Error`, `ExpressionDelimitedSeparator`, and `ExpressionDelimitedForeignClose` groups.

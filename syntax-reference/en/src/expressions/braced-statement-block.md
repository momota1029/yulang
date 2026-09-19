# Brace-delimited statement block

## 1. Authority and scope

This page defines `BracedStatementBlockExpression` in `syntax-v0`.
The 2026-08-20 `yu-syntax` architecture defines its accepted grammar and direct Rowan CST.
The Authoritative 2026-09-08 braced canonical Statement-sequence recovery record defines its required-statement, separator, and local-close recovery.

The page covers an operand-starting brace block, its direct canonical statements, separators, close, and recovery CST.
It does not define record literals or fields, control-flow brace bodies, `CatchBlock`, brace-local spread syntax, HIR interpretation, types, diagnostics wording, or formatting.

## 2. Accepted syntax

```text
BracedStatementBlockExpression :=
    "{" G*
    [ Statement { BraceStatementSeparator Statement } [ BraceStatementSeparator ] ]
    G0 "}"
BraceStatementSeparator := G0 ("," | ";") G* | qualifying current-depth newline
```

The block may be empty.
Comma, semicolon, and qualifying current-depth newline separate completed statements.
A deeper newline stays within the current statement.
Each separator form may be trailing and does not create an empty statement.

## 3. Admission and boundaries

At an operand-required position, a lone `{` admits this primary and commits its matching brace scope.
The block owns its current-depth statement separators and its local close.
Outer stops, separators, and closes remain suspended until this scope returns.

Before a required statement and after a separator, matching `}` is a local block boundary.
Nested delimiters and lexical regions cannot donate a separator or close to the outer block.
Within `{x: 1, y: 2}`, the block-owned comma ends the first statement, so each statement may contain an ordinary one-argument colon application.

## 4. Direct Rowan CST

`BracedStatementBlockExpression` is a direct primary child of `OperatorChain`.
It contains `LBrace`, opening trivia, direct `Statement` children, `BlockStatementSeparator` children, closing trivia, and `RBrace` in source order.
Every comma, semicolon, and qualifying newline separator has one `BlockStatementSeparator` wrapper.
A comma or semicolon wrapper owns its `G0`, literal punctuation, and following trivia.
A newline wrapper contains its native trivia leaf and creates no synthetic token.
The node contains neither a record wrapper nor an empty `Statement` node.

```text
BracedStatementBlockExpression := LBrace { Statement | BlockStatementSeparator | trivia } RBrace
BlockStatementSeparator := G0 (Comma | Semicolon) G* | qualifying current-depth newline trivia
Statement := OperatorChain | canonical statement form
```

## 5. Recovery CST

In a required-statement phase, comma or semicolon places one zero-width `Missing` in `BracedStatementBlock(Statement)` and leaves the punctuation for its separator phase.
A non-boundary non-statement run is one maximal non-empty raw `Error` group in that same statement slot; a later admitted statement retries it.
An error that reaches a separator, qualifying newline, close, nonlocal close, fence, or EOF adds no same-cause missing node.

A newly admitted separate statement after a completed statement without a separator places one zero-width `Missing` in `BracedStatementBlock(Separator)`.
Valid empty blocks, multiline applications, and trailing separators add no fabricated statement missing node.
An absent local `}` places one zero-width `Missing` in `ClosingDelimiter { BracedStatementBlockExpression, Brace }`.
Every nonlocal close remains unconsumed for its actual owner.

Initial leading before an error remains native block content, interior leading belongs to `Error`, and retry or protected-boundary leading remains pending.
Nested statements retain their own recovery roles.

## 6. Source/CST examples

`{}` is an empty valid block.

```xml
<BracedStatementBlockExpression>
  <LBrace text="{" /><RBrace text="}" />
</BracedStatementBlockExpression>
```

`{x, y}` places both statements and one comma separator wrapper directly in the block.

```xml
<BracedStatementBlockExpression>
  <LBrace text="{" />
  <Statement><OperatorChain><IdentifierExpression><Identifier text="x" /></IdentifierExpression></OperatorChain></Statement>
  <BlockStatementSeparator><Comma text="," /><Whitespace text=" " /></BlockStatementSeparator>
  <Statement><OperatorChain><IdentifierExpression><Identifier text="y" /></IdentifierExpression></OperatorChain></Statement>
  <RBrace text="}" />
</BracedStatementBlockExpression>
```

`{x,}` is valid: it has one `Statement`, one trailing `BlockStatementSeparator`, and no `Missing` node.

`{x: 1, y: 2}` has two direct statements; its comma is the block separator, while each statement contains its own ordinary `ColonApplicationTail`.

## 7. Composition

[Dynamic operator chains](operator-chain.md) define the block's primary position.
The [layout-aware separator authority](../cross-cutting/layout-aware-separator-authority.md) defines qualifying current-depth newline boundaries.
[Colon application](colon-application.md) operates inside an individual statement and returns block separators to this block.

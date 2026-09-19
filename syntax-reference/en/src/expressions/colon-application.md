# Colon application

## 1. Authority and scope

This page defines the terminal `ColonApplicationTail` in `syntax-v0`.
The 2026-08-20 `yu-syntax` architecture defines its accepted grammar and direct Rowan CST.
The Authoritative 2026-09-08 Colon/With inline, indented-Statement role-transport, and Colon layout-sequence records define its current recovery and current-depth sequence ownership.
See the [syntax content model](../conventions/syntax-content-model.md), [Rowan CST notation](../conventions/rowan-cst.md), and [recovery `Error` and `Invalid` topology](../conventions/recovery-error-invalid-topology.md) for shared notation.

The page covers a completed chain followed by a lone colon, its inline arguments or indented statement block, and their recovery CST.
It does not define the colon forms owned by `if`, declarations, patterns, or types; target association; call or record interpretation; HIR; types; diagnostics wording; or formatting.

## 2. Accepted syntax

```text
ColonApplicationTail := ":" ColonBody
ColonBody := InlineColonArguments | IndentedStatementBlock
InlineColonArguments := OperatorChain { ColonArgumentBoundary OperatorChain }
ColonArgumentBoundary := "," | qualifying current-depth newline
```

A physical newline immediately after `:` selects `IndentedStatementBlock` only when its following indentation is strictly deeper than the captured base.
Otherwise the first body is one inline `OperatorChain`.
With no outer current-depth sequence owner, the tail owns later literal commas and qualifying newlines.
With an outer owner, it parses one inline argument and returns that owner's boundary.

## 3. Admission and boundaries

Only an unreserved lone `:` after an operand-complete `OperatorChain` admits this terminal tail.
`::` is not split.
An active colon stop, ML mode, a close, an outer separator, or an owner boundary returns before admission.
After admission, the tail ends the enclosing chain.

The layout decision precedes the sequence-owner query.
An equal-or-shallower post-colon newline leaves the newline and following item with the outer owner.
For a colon-owned inline sequence, a qualifying newline has following indentation at most the captured base; a deeper newline remains continuation trivia.
A comma together with surrounding qualifying newline is one boundary episode, so it creates neither an empty argument nor a synthetic separator.
A final qualifying newline before end is a valid terminal boundary.

## 4. Direct Rowan CST

`ColonApplicationTail` is a direct, terminal child of `OperatorChain` and does not contain its target.
It contains `Colon`, its owned trivia, and either direct RHS `OperatorChain` children with literal commas or one direct `IndentedStatementBlock`.
Qualifying newline separators remain trivia; they create no separator node or synthetic token.

```text
OperatorChain := <completed-chain children> ColonApplicationTail
ColonApplicationTail := Colon (OperatorChain { Comma OperatorChain } | IndentedStatementBlock)
```

An outer sequence keeps its comma or qualifying newline outside `ColonApplicationTail`.
Nested colon application is a child of its nested argument chain, not another terminal child of the outer chain.

## 5. Recovery CST

An accepted colon with no inline RHS places one zero-width `Missing` in `ColonApplication(Rhs)`.
A colon-owned leading comma places one zero-width missing first argument; a required argument after a literal comma is missing at EOF or another protected boundary.
A tail owned by an outer sequence leaves that comma or qualifying newline unconsumed and adds no colon argument recovery for it.

A non-boundary, non-NUD inline run is one maximal raw `Error` group in `ColonApplication(Rhs)` or `ColonApplication(InlineArgument)`.
An admitted value then retries the same slot.
Initial malformed-slot leading is native tail content; interior leading belongs to `Error`; retry and boundary leading remain for their owner.
When an error reaches a protected boundary, it adds no same-cause `Missing`.

The indented alternative transports `ColonApplication(IndentedStatement)` to the shared block entry and required child-statement slots.
Its block recovery remains in `IndentedStatementBlock`; the colon tail adds no duplicate node.
All `Missing` nodes are zero-width, and raw `Error` groups are non-empty.

## 6. Source/CST examples

`a + b: x` puts the completed chain before the target-free tail.

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="a" /></IdentifierExpression>
  <Whitespace text=" " />
  <InfixOperatorUse><Operator text="+" /></InfixOperatorUse>
  <Whitespace text=" " />
  <IdentifierExpression><Identifier text="b" /></IdentifierExpression>
  <ColonApplicationTail>
    <Colon text=":" /><Whitespace text=" " />
    <OperatorChain><IdentifierExpression><Identifier text="x" /></IdentifierExpression></OperatorChain>
  </ColonApplicationTail>
</OperatorChain>
```

At root, `f: x, y` gives the tail both inline arguments.

```xml
<ColonApplicationTail>
  <Colon text=":" /><Whitespace text=" " />
  <OperatorChain><IdentifierExpression><Identifier text="x" /></IdentifierExpression></OperatorChain>
  <Comma text="," /><Whitespace text=" " />
  <OperatorChain><IdentifierExpression><Identifier text="y" /></IdentifierExpression></OperatorChain>
</ColonApplicationTail>
```

The following source selects the shared indented block.

```text
f:
  x
  y
```

Its tail contains `Colon` and one direct `IndentedStatementBlock`; the block owns its opening trivia and statement sequence.

## 7. Composition

[Dynamic operator chains](operator-chain.md) define the enclosing terminal-continuation position.
The [layout-aware separator authority](../cross-cutting/layout-aware-separator-authority.md) defines qualifying current-depth newline boundaries.
The shared `IndentedStatementBlock` owns an indented body's statement sequence and transported recovery slots.

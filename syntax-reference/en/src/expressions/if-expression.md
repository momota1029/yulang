# `if` expression

## 1. Authority and scope

This page defines `IfExpression` in `syntax-v0`.
The 2026-08-20 `yu-syntax` architecture defines its accepted grammar and direct Rowan CST.
The Authoritative 2026-09-08 required-operand and If current-Item recovery records define its condition, introducer, and body recovery.
The indented-Statement transport and Colon layout-sequence records define the shared body boundaries.

The page covers `if`, sibling `elsif` arms, an optional `else` arm, direct arm CST, and recovery in their required slots.
It does not define branch values, branch typing or effects, operator association, brace arm bodies, HIR, diagnostics wording, or formatting.

## 2. Accepted syntax

```text
IfExpression := IfArm { IfContinuation ElsifArm } [ IfContinuation ElseArm ]
IfArm := IfKw G* Condition Gcont ColonIntroducedArmBody
ElsifArm := ElsifKw G* Condition Gcont ColonIntroducedArmBody
ElseArm := ElseKw Gcont (ColonIntroducedArmBody | OperatorChain)
Condition := OperatorChain under current-depth StopSet { Colon, LeftBrace, Elsif, Else }
ColonIntroducedArmBody := ":" (InlineArmExpression | IndentedStatementBlock)
InlineArmExpression := OperatorChain
IfContinuation := horizontal trivia | newline with next indent >= if base indent
Gcont := chain-continuing trivia under the active If companion boundary
```

`elsif` is one exact contextual word.
`else if` is an `ElseArm` with a nested `IfExpression` body, not an `elsif` arm.
An arm colon owns exactly one inline body chain unless a strictly deeper post-colon newline selects `IndentedStatementBlock`.

## 3. Admission and boundaries

Only the exact maximal word `if` admits an operand-starting primary; `ifx` remains an identifier.
The active expression's companion frame, rather than ordinary NUD word admission, recognizes `elsif` and `else` as arm boundaries.
The condition stops before `:`, `{`, `elsif`, or `else`, so an arm colon is never `ColonApplicationTail`.

The expression captures its base indentation once.
Only horizontal continuation or a newline at that base or deeper can lead to a sibling arm.
A shallower continuation or non-keyword continuation remains with the outer owner.
The companion frame lasts across every `elsif` arm and ends before parsing the expression's own else body.

## 4. Direct Rowan CST

`IfExpression` is a direct primary child of `OperatorChain`.
It contains one `IfArm`, zero or more sibling `IfArm` nodes beginning with `ElsifKw`, and at most one `ElseArm`, all in source order.
Each `IfArm` contains a direct `Condition`, which contains its `OperatorChain`.
Each colon-introduced arm body directly contains `Colon` and either its inline `OperatorChain` or an `IndentedStatementBlock`.
There is no generic colon-application or inline-list wrapper for an arm body.

```text
IfExpression := IfArm { ElsifArm } [ ElseArm ]
IfArm := (IfKw | ElsifKw) Condition Colon (OperatorChain | IndentedStatementBlock)
Condition := OperatorChain
ElseArm := ElseKw (Colon (OperatorChain | IndentedStatementBlock) | OperatorChain)
```

## 5. Recovery CST

An absent condition uses one zero-width `Missing` in `IfExpression(Condition)`.
At `if` EOF, it does not cascade introducer or body missing nodes.
After a retained condition, absence of the required colon/body is one arm-body absence; after an accepted colon, an absent body is one body missing node.
An equal-or-shallower post-colon newline stays with the outer owner.

A malformed inline body is one maximal non-empty raw `Error` group, then retries the same body slot.
An accepted `elsif` or `else` retains its keyword and emits its appropriate missing body rather than rolling back to an identifier.
After the first `ElseArm`, the expression finishes and leaves a later `else` for outer recovery.

The shared required-operand kernel supplies condition recovery, and an indented body transports `IfExpression(IndentedStatement)` to the block's entry and child slots.
Missing nodes are zero-width; raw `Error` groups are non-empty; nested recovery remains in its nested owner.

## 6. Source/CST examples

`if x: 1 else: 0` has arm-owned colons and no colon-application node.

```xml
<IfExpression>
  <IfArm>
    <IfKw text="if" /><Whitespace text=" " />
    <Condition><OperatorChain><IdentifierExpression><Identifier text="x" /></IdentifierExpression></OperatorChain></Condition>
    <Colon text=":" /><Whitespace text=" " />
    <OperatorChain><IntegerLiteral text="1" /></OperatorChain>
  </IfArm>
  <Whitespace text=" " />
  <ElseArm>
    <ElseKw text="else" /><Colon text=":" /><Whitespace text=" " />
    <OperatorChain><IntegerLiteral text="0" /></OperatorChain>
  </ElseArm>
</IfExpression>
```

`if x: 1 elsif y: 2 else: 0` contains two sibling `IfArm` nodes before its `ElseArm`.

```text
if x:
  1
  2
else: 0
```

The first arm has one direct `IndentedStatementBlock` with two direct `Statement` children; the dedented `else` returns to the enclosing `IfExpression`.

## 7. Composition

[Dynamic operator chains](operator-chain.md) define the primary's value position and body chains.
[Colon application](colon-application.md) remains available inside a body chain but does not own an arm colon.
The [layout-aware separator authority](../cross-cutting/layout-aware-separator-authority.md) and shared indented block define current-depth body boundaries.

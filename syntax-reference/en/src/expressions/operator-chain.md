# Dynamic operator chains

## 1. Authority and scope

This page defines `OperatorChain` in `syntax-v0`.
Its accepted syntax and flat direct Rowan CST follow the precedence-neutral dynamic-operator-chain amendment in the 2026-08-20 `yu-syntax` architecture.
The 2026-09-08 required-operand current-Item recovery defines operand recovery.
See the [syntax content model](../conventions/syntax-content-model.md) and [Rowan CST notation](../conventions/rowan-cst.md) for shared syntax and recovery notation.

The page covers operator roles, primaries, fixed postfixes, ML arguments, annotations, terminal outer tails, and operand-slot recovery.
It does not define binding-power association, HIR, types, operator values, or execution semantics.

## 2. Accepted syntax

```text
OperatorChain := OperandSlot { Continuation } [ TerminalOuterContinuation ]
OperandSlot := { PrefixOperatorUse G* } (PrimaryHead | NullfixOperatorUse)
Continuation := FixedPostfixContinuation
              | G* SuffixOperatorUse
              | G* InfixOperatorUse G* OperandSlot
              | MlApplicationContinuation
              | G* TypeAnnotationContinuation
FixedPostfixContinuation := CallTail | IndexTail | FieldTail | ProjectionTail | PathTail
MlApplicationContinuation := MlArgumentSeparator MlArgument
MlArgument := OperatorChain under the ml_arg stop scope
TerminalOuterContinuation := ColonApplicationTail | AssignmentTail | WithBodyTail
```

An operator spelling is accepted only in a role that the exact syntax environment permits at that position.
The same spelling can have prefix, infix, suffix, or nullfix roles.
`=` can become `AssignmentTail` only after an admitted dynamic LED operator has declined.

## 3. Admission and boundaries

A value position admits a primary, a nullfix use, or an accepted prefix sequence.
An operand-complete position considers fixed punctuation tails, the ML boundary, annotation, terminal outer tail, suffix, and infix in their structural priority.
Numeric binding power does not take part in that choice or in CST parent-child ownership.

Active stops, delimiters, structural terminators, and ambient owner boundaries return to the caller unconsumed.
A terminal outer continuation ends the chain.
A fixed postfix or ML application leaves the chain in its operand-complete position.

## 4. Direct Rowan CST

`OperatorChain` places primaries, operator-use nodes, fixed-tail nodes, nested `MlArgument` chains, annotations, and terminal tails in source order.
`PrefixOperatorUse`, `InfixOperatorUse`, `SuffixOperatorUse`, and `NullfixOperatorUse` each retain one accepted spelling.
The CST adds no left or right operand edge and no application subtree.

A fixed tail does not contain its target as a child; it owns only its own delimiter or required slot as nested CST.
The argument of `MlArgument` is a nested `OperatorChain`.
`AssignmentTail`, colon application, and a `with:` body are terminal children.

## 5. Recovery CST

A unique dangling prefix or infix role retains its operator-use node and places one zero-width `Missing` in the required operand slot.
A non-boundary, non-NUD run becomes one maximal raw `Error` group directly in the chain.
If an operand is admitted after that group, it retries the same slot.
A raw group that reaches a safe boundary is the recovered operand and adds no same-cause `Missing`.

An unresolvable operator-shaped spelling receives no role node.
`Missing` or raw `Error` in a nested construct remains in that construct's slot and does not move into the outer operand slot.
`Invalid` does not wrap ordinary operator-operand recovery.

## 6. Source/CST examples

When `+` is available as an infix role, `-` as a prefix role, and `!` as a suffix role, `-a + b!` has this source order.

```xml
<OperatorChain>
  <PrefixOperatorUse><Operator text="-" /></PrefixOperatorUse>
  <IdentifierExpression><Identifier text="a" /></IdentifierExpression>
  <InfixOperatorUse><Operator text="+" /></InfixOperatorUse>
  <IdentifierExpression><Identifier text="b" /></IdentifierExpression>
  <SuffixOperatorUse><Operator text="!" /></SuffixOperatorUse>
</OperatorChain>
```

In the same environment, `a +` retains the infix use and recovers its operand slot.

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="a" /></IdentifierExpression>
  <Whitespace text=" " />
  <InfixOperatorUse><Operator text="+" /></InfixOperatorUse>
  <Missing />
</OperatorChain>
```

## 7. Composition

Construct pages own parenthesized elements, fixed tails, and terminal tails.
A later association phase derives an associated result from the same flat item sequence and exact association environment, but does not rewrite the CST.
Changing numeric binding power alone does not change the surface `OperatorChain` shape.

# Call, field, path, and ML-application tails

## 1. Authority and scope

This page defines `CallTail`, `FieldTail`, `PathTail`, and `MlArgument` in `syntax-v0`.
Their accepted syntax and direct Rowan CST follow the fixed-tail sections of the 2026-08-20 `yu-syntax` architecture.
The expression-delimited current-Item recovery, raw-slot CST, fixed-tail recovery, and ML separator-leading ownership amendments define the recovery and source-ownership rules used here.
The 2026-09-08 fixed-tail recovery amendment and 2026-09-10 CST slot schema catalog define FieldTail and PathTail recovered-slot handoff.
The [layout-aware comma-or-newline-delimited sequence authority](../cross-cutting/layout-aware-separator-authority.md) defines the captured base and qualifying-newline boundary for call items.
See the [syntax content model](../conventions/syntax-content-model.md), [Rowan CST notation](../conventions/rowan-cst.md), and [recovery `Error` and `Invalid` topology](../conventions/recovery-error-invalid-topology.md) for shared syntax-v0 notation and recovery elements.

The page covers source-order continuations after a completed operand.
It does not define index or projection tails, terminal tails, operator association, name resolution, types, execution semantics, diagnostics wording, or formatting.

## 2. Accepted syntax

```text
FixedPostfixContinuation := CallTail
                           | ChainContinuingTrivia FieldTail
                           | ChainContinuingTrivia PathTail

ChainContinuingTrivia := maximal G* with no physical newline
                        | maximal G* whose following-line indent is deeper than the active base

CallTail := "(" G*
            [ OperatorChain { CallSeparator OperatorChain } [ CallSeparator ] ]
            ")"
CallSeparator := "," | ";" | qualifying current-depth newline

FieldTail := "." Identifier
PathTail := "::" G* PathSegment
PathSegment := Identifier | SigilIdentifier

MlApplicationContinuation := MlArgumentSeparator MlArgument
MlArgumentSeparator := non-empty trivia with no physical newline
                     | trivia with a physical newline whose following indent is deeper than the active base
MlArgument := OperatorChain under the ML-argument stop scope
```

The call opener is adjacent to its completed operand.
`ChainContinuingTrivia` is empty, same-line, or deeper-line trivia at the outer-chain level.
The dot and identifier of a field tail are adjacent.
Field and path tails follow `ChainContinuingTrivia`, and `PathTail` accepts its maximal `G*` after `::`.
A call accepts comma, semicolon, and a qualifying current-depth newline in its item list.

## 3. Admission and boundaries

At an operand-complete position, active stops, matching closes, and an equal-or-shallower newline return to their owners before a tail is admitted.
An accepted dynamic spelling also keeps its dynamic role.
After those decisions, an adjacent `(` admits `CallTail`.
An exact `.identifier` admits `FieldTail` after `ChainContinuingTrivia`, and exact `::` admits `PathTail` after `ChainContinuingTrivia`.
The projection forms `.(` and `.{` take precedence over field recovery, and a longer accepted dot spelling is not split into a field tail.

ML application requires both a qualifying non-empty trivia run and a shared `OperatorChain` NUD candidate.
Thus `f(x)` has a call tail, while `f (x)` has an ML argument whose nested chain starts with a parenthesized expression.
An equal-or-shallower newline is not an ML separator.
After one admitted ML argument, later qualifying separator trivia belongs to the enclosing chain, where it can introduce a sibling ML argument.

Call items stop at a literal separator, the matching `)`, or a qualifying current-depth newline.
Within a call item, a colon application takes one right-hand-side chain and returns the list boundary to the call.
An ML continuation that qualifies inside an item remains in that item.
After a fixed tail closes or recovers its close, the surrounding `OperatorChain` resumes its operand-complete position.

## 4. Direct Rowan CST

All four forms are source-order children of `OperatorChain`.
A tail does not contain its target expression.

`CallTail` directly contains its `LParen`, opening and inter-item trivia, nested argument `OperatorChain` nodes, literal `Comma` or `Semicolon` leaves, and `RParen`.
A qualifying newline remains trivia; it creates neither a separator node nor a synthetic token.
`FieldTail` directly contains `Dot` and `Identifier`.
`PathTail` directly contains `ColonColon`, its post-separator trivia, and `Identifier` or `SigilIdentifier`.
`ChainContinuingTrivia` before a field or path tail is direct native content of the enclosing `OperatorChain`.
It is outside the tail's source range.

The separator leading before an admitted ML argument is direct native content of the enclosing `OperatorChain`.
`MlArgument` starts at the argument payload and directly contains its nested `OperatorChain`.
The separator leading belongs neither to `MlArgument` nor to that nested chain.

## 5. Recovery CST

`f()` is an empty call and has no argument `Missing`.
A leading or repeated call separator places one zero-width `Missing` in the absent item slot before the literal separator.
An admitted next item on the same line without a separator places one zero-width `Missing` in the separator slot and retries the item at the same position.
An ML continuation that is valid for the current item remains one item and does not cause separator recovery.

A malformed call item is one maximal non-empty raw `Error` group in the call owner, then a later item may retry the same slot.
An absent matching close places one zero-width `Missing` in the close slot and leaves a protected outer boundary unconsumed.
An unprotected foreign close is a raw `Error` group in `ExpressionDelimitedForeignClose`.
A rejected call-separator run is a raw `Error` group in `ExpressionDelimitedSeparator`.
Each wrapper contains exactly one non-empty contiguous group and contains no `Missing`, accepted punctuation, retry leading, or `Invalid`.

After an accepted dot, an absent field name places a zero-width `Missing` in the field-name slot.
After an accepted `::`, an absent path segment places a zero-width `Missing` in the path-segment slot.
A malformed name or segment is one maximal non-empty raw `Error` group in its tail.
Each recovered field-name or path-segment slot is terminal for that tail.
The tail hands any retained Item, including its leading, to the outer tail; a later continuation is a sibling of the recovered tail, not a replacement for its name or segment.
The forms `..`, `...`, `.(`, and `.{` do not become a field tail plus recovery.

No ML node is created when its separator has no shared NUD candidate.
If an admitted ML argument lacks an operand, the nested `OperatorChain` owns that operand recovery; `MlArgument` adds none.

## 6. Source/CST examples

`f(x, y)` keeps the call punctuation and argument chains in the tail.

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="f" /></IdentifierExpression>
  <CallTail>
    <LParen text="(" />
    <OperatorChain><IdentifierExpression><Identifier text="x" /></IdentifierExpression></OperatorChain>
    <Comma text="," />
    <Whitespace text=" " />
    <OperatorChain><IdentifierExpression><Identifier text="y" /></IdentifierExpression></OperatorChain>
    <RParen text=")" />
  </CallTail>
</OperatorChain>
```

`f x y` has two sibling ML arguments, and each separating space is owned by the outer chain.

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="f" /></IdentifierExpression>
  <Whitespace text=" " />
  <MlArgument><OperatorChain><IdentifierExpression><Identifier text="x" /></IdentifierExpression></OperatorChain></MlArgument>
  <Whitespace text=" " />
  <MlArgument><OperatorChain><IdentifierExpression><Identifier text="y" /></IdentifierExpression></OperatorChain></MlArgument>
</OperatorChain>
```

`a .b :: c` keeps the continuing trivia outside each fixed tail.

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="a" /></IdentifierExpression>
  <Whitespace text=" " />
  <FieldTail><Dot text="." /><Identifier text="b" /></FieldTail>
  <Whitespace text=" " />
  <PathTail><ColonColon text="::" /><Whitespace text=" " /><Identifier text="c" /></PathTail>
</OperatorChain>
```

## 7. Composition

[Dynamic operator chains](operator-chain.md) define the outer source-order chain and its dynamic roles.
[Index and projection tails](index-projection-tails.md) define the remaining fixed postfixes.
The shared recovery topology defines how direct raw `Error` groups and the two expression-delimited raw-slot wrappers are interpreted.

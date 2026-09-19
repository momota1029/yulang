# Index and projection tails

## 1. Authority and scope

This page defines `IndexTail`, `ProjectionTupleTail`, `ProjectionRecordTail`, and `ProjectionRecordSpreadItem` in `syntax-v0`.
Their accepted syntax and direct Rowan CST follow the index and projection fixed-tail sections of the 2026-08-20 `yu-syntax` architecture.
The expression-delimited current-Item recovery and raw-slot CST amendments define the shared delimited recovery topology used by these tails.
The [layout-aware comma-or-newline-delimited sequence authority](../cross-cutting/layout-aware-separator-authority.md) defines the captured base and qualifying-newline boundary for their item lists.
See the [syntax content model](../conventions/syntax-content-model.md), [Rowan CST notation](../conventions/rowan-cst.md), and [recovery `Error` and `Invalid` topology](../conventions/recovery-error-invalid-topology.md) for shared syntax-v0 notation and recovery elements.

The page covers source-order index and projection continuations, their delimited items, and record-projection spread items.
It does not define semantic indexing or projection, record validation, spread position or multiplicity validation, operator association, name resolution, types, execution semantics, diagnostics wording, or formatting.

## 2. Accepted syntax

```text
FixedPostfixContinuation += IndexTail | ChainContinuingTrivia ProjectionTail

ChainContinuingTrivia := maximal G* with no physical newline
                        | maximal G* whose following-line indent is deeper than the active base

IndexTail := "[" G*
             [ OperatorChain { IndexSeparator OperatorChain } [ IndexSeparator ] ]
             "]"
ProjectionTail := ProjectionTupleTail | ProjectionRecordTail
ProjectionTupleTail := ".(" G*
                       [ OperatorChain { ProjectionTupleSeparator OperatorChain } [ ProjectionTupleSeparator ] ]
                       ")"
ProjectionRecordTail := ".{" G*
                        [ ProjectionRecordItem { ProjectionRecordSeparator ProjectionRecordItem } [ ProjectionRecordSeparator ] ]
                        "}"
ProjectionRecordItem := OperatorChain | ProjectionRecordSpreadItem
ProjectionRecordSpreadItem := ".." G* OperatorChain

IndexSeparator := "," | ";" | qualifying current-depth newline
ProjectionTupleSeparator := "," | ";" | qualifying current-depth newline
ProjectionRecordSeparator := "," | ";" | qualifying current-depth newline
```

`[` is adjacent to the completed operand for an index tail.
`ChainContinuingTrivia` is empty, same-line, or deeper-line trivia at the outer-chain level.
A projection has an adjacent dot and opener after `ChainContinuingTrivia`.
Thus `a.(x)` and `a.{x}` are projections, while `a. (x)` and `a. {x}` are not.
Only a record-projection item position gives exact `..` spread authority.
Index and tuple-projection items do not admit a spread item.

## 3. Admission and boundaries

At an operand-complete position, active stops, matching closes, and equal-or-shallower newlines return to their owners before a fixed tail is admitted.
An accepted dynamic spelling keeps its dynamic role.
With no leading trivia, `[` admits `IndexTail`.
Exact `.(` and `.{` admit projection after `ChainContinuingTrivia` and before field recovery.
Each accepted introducer claims its tail; the enclosing chain resumes only after that tail closes or recovers its close.

An index item stops at a literal separator, `]`, or a qualifying current-depth newline.
A tuple-projection item uses the corresponding `)` boundary, and a record-projection item uses the corresponding `}` boundary.
Each tail accepts comma, semicolon, and a qualifying current-depth newline as item boundaries.
A deeper newline remains continuation trivia in the current item.

Within an item, a colon application takes one right-hand-side chain and returns the container boundary to its tail.
An ML continuation that qualifies in an item remains part of that item.
An equal-or-shallower newline returns to the delimited owner rather than becoming an ML separator.

## 4. Direct Rowan CST

`IndexTail`, `ProjectionTupleTail`, and `ProjectionRecordTail` are direct source-order children of `OperatorChain`.
They do not contain their target expression.
There is no generic `ProjectionTail` CST wrapper.

`IndexTail` directly contains `LBracket`, item `OperatorChain` nodes, literal separators, trivia, and `RBracket`.
`ProjectionTupleTail` directly contains `Dot`, `LParen`, item `OperatorChain` nodes, literal separators, trivia, and `RParen`.
`ProjectionRecordTail` directly contains `Dot`, `LBrace`, ordinary item `OperatorChain` nodes or `ProjectionRecordSpreadItem` nodes, literal separators, trivia, and `RBrace`.
Qualifying newline separators remain trivia and create neither separator nodes nor synthetic tokens.
`ChainContinuingTrivia` before a projection is direct native content of the enclosing `OperatorChain`.
It is outside the projection tail's source range.

`ProjectionRecordSpreadItem` directly contains `DotDot`, its following trivia, and one nested right-hand-side `OperatorChain`.
The exact marker is not split from a longer operator-shaped spelling.

## 5. Recovery CST

`a[]`, `a.()`, and `a.{}` are empty tails and have no item `Missing`.
A leading or repeated literal separator places one zero-width `Missing` in the absent item slot before that separator.
An admitted same-line next item without a separator places one zero-width `Missing` in the separator slot and retries that item at the same position.
A valid ML continuation remains in the current item and does not cause separator recovery.

A malformed item is one maximal non-empty raw `Error` group in its delimited owner, then a later ordinary item or exact spread item may retry the same slot.
An absent matching close places one zero-width `Missing` in the close slot and leaves a protected outer boundary unconsumed.
An unprotected foreign close is a raw `Error` group in `ExpressionDelimitedForeignClose`.
A rejected separator run is a raw `Error` group in `ExpressionDelimitedSeparator`.
Each wrapper contains exactly one non-empty contiguous group and contains no `Missing`, accepted punctuation, retry leading, or `Invalid`.

After an exact `..`, an absent record-spread right-hand side places one zero-width `Missing` in that right-hand-side slot without consuming the separator or close.
A malformed spread right-hand side is one maximal non-empty raw `Error` group and may retry the same slot.
Longer spellings such as `...` and `..+` do not become `DotDot` plus recovery.
A malformed colon application inside an ordinary item recovers in that nested tail; the projection tail adds no duplicate recovery.

## 6. Source/CST examples

`a[i; j]` places both index items and the literal semicolon in `IndexTail`.

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="a" /></IdentifierExpression>
  <IndexTail>
    <LBracket text="[" />
    <OperatorChain><IdentifierExpression><Identifier text="i" /></IdentifierExpression></OperatorChain>
    <Semicolon text=";" />
    <Whitespace text=" " />
    <OperatorChain><IdentifierExpression><Identifier text="j" /></IdentifierExpression></OperatorChain>
    <RBracket text="]" />
  </IndexTail>
</OperatorChain>
```

`a .(x, y)` keeps the continuing space in the outer chain and uses the tuple-projection tail rather than a field tail.

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="a" /></IdentifierExpression>
  <Whitespace text=" " />
  <ProjectionTupleTail>
    <Dot text="." /><LParen text="(" />
    <OperatorChain><IdentifierExpression><Identifier text="x" /></IdentifierExpression></OperatorChain>
    <Comma text="," /><Whitespace text=" " />
    <OperatorChain><IdentifierExpression><Identifier text="y" /></IdentifierExpression></OperatorChain>
    <RParen text=")" />
  </ProjectionTupleTail>
</OperatorChain>
```

`a.{..rest}` gives the spread marker and its right-hand-side chain their own item node.

```xml
<OperatorChain>
  <IdentifierExpression><Identifier text="a" /></IdentifierExpression>
  <ProjectionRecordTail>
    <Dot text="." /><LBrace text="{" />
    <ProjectionRecordSpreadItem>
      <DotDot text=".." />
      <OperatorChain><IdentifierExpression><Identifier text="rest" /></IdentifierExpression></OperatorChain>
    </ProjectionRecordSpreadItem>
    <RBrace text="}" />
  </ProjectionRecordTail>
</OperatorChain>
```

## 7. Composition

[Dynamic operator chains](operator-chain.md) define the enclosing source-order chain and its other continuations.
[Call, field, path, and ML-application tails](call-field-path-tails.md) define the sibling fixed tails and ML continuation.
The shared recovery topology defines how direct raw `Error` groups and the two expression-delimited raw-slot wrappers are interpreted.

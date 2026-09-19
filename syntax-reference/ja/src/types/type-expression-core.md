# Standalone `TypeExpression` core

## 1. 正本と対象範囲

このページは`syntax-v0`のcore `TypeExpression` formを定める。2026年8月20日の
syntax architectureにあるAuthoritativeなtype-expression section、Type
contextual-boundary correction、PathSegment/TypeCall recovery amendment、
accepted-input recovery authorityに従う。

atom、path、call、ML-style application、arrow、parenthesized groupを対象とする。
named record、`forall`、effect row、polymorphic variant、bracket rowは各ページで
定める。type meaning、lowering、diagnostic wordingは対象外である。

## 2. 受理構文

```text
TypeExpression := TypePrimary { TypeTightTail | TypeApplyArgument } [ TypeArrowTail ]
TypePrimary := TypeAtom | ParenthesizedTypeGroup
TypeAtom := Identifier | SigilIdentifier | Number
TypeTightTail := TypePathTail | TypeCallTail
TypePathTail := TypeChainTrivia "::" TypeChainTrivia TypePathSegment
TypePathSegment := Identifier | SigilIdentifier
TypeCallTail := "(" G* [ TypeExpression { TypeDelimitedSeparator TypeExpression } [ TypeDelimitedSeparator ] ] ")"
TypeApplyArgument := TypeApplyBoundary TypeExpressionInTypeMlScope
TypeArrowTail := TypeChainTrivia "->" TypeChainTrivia TypeExpression
ParenthesizedTypeGroup := "(" G* [ TypeExpression { TypeDelimitedSeparator TypeExpression } [ TypeDelimitedSeparator ] ] ")"
TypeDelimitedSeparator := comma | semicolon | qualifying newline
```

`Number`はprimaryだがpath segmentではない。qualifying newlineはdelimited itemを
区切る。deeper newlineはtype-continuation triviaに残る。

## 3. 受理と境界

tail judgeはactive stop、close、equal-or-shallower caller boundaryで先に返る。
leading triviaがなければ`->`、adjacent `(`、`::`を認識する。Type-ML argumentでは
nonempty triviaが先にnested argumentを終え、その後にtrivia-qualified arrow、path、
applyを判定する。

`List(Int)`はcall、`List (Int)`はapplyである。`F A::B`のpathはapplied argument内、
`F A ::B`のpathはouter typeに属する。arrowは完全なRHSを所有するため`A -> B -> C`
はright-associativeになる。same-line name-shaped path segmentはcontextual word
boundaryより優先するが、newline-bearing contextual boundaryはcallerに残る。committed
callはfresh nested type scopeを作り、return後にenclosing boundaryを復元する。

## 4. Direct Rowan CST

`TypeExpression`はprimary、source-orderの`TypePathTail`、`TypeCallTail`、
`TypeApplyArgument`、最大一つの`TypeArrowTail`を持つ。`ParenthesizedTypeGroup`と
`TypeCallTail`はpunctuation、trivia、direct `TypeExpression` itemをsource orderで持つ。

`TypePathTail`は`::`、trivia、segmentを持つ。apply boundaryとargumentは
`TypeApplyArgument`で表す。groupにはsynthetic grouping、tuple、separator nodeを
作らず、literal punctuationとnewline triviaをsource-bearing childとして残す。

## 5. Recovery CST

required primary、path segment、delimited item/separator、close、arrow RHSのslotには
zero-widthの`Missing`を置く。malformed primary、path segment、call item、arrow RHSは
そのslotのraw `Error` groupとなる。valid retryは同じslotを満たす。apply trivia後に
primaryがなければapplyもsynthetic `Missing`も作らない。

Path recoveryはprotected caller boundaryを消費しない。TypeCallはargument、separator、
close recoveryを分け、argument後のadmitted residualはterminal close recoveryに属する。
Parenthesized groupとeffect rowはlocally consumed mismatched closeにだけ
`TypeDelimitedForeignClose`を使う。ほかのraw type recoveryはdirectである。

## 6. Source/CST例

`List(Int)::Result Arg -> Out -> Final`はsource orderでcall tail、path tail、apply
argument、arrow tailを持つ。RHSが二つ目のarrowを所有する。

`(A)`はgrouped typeである。`(A,)`と`(A;)`はtrailing punctuationを保持する
tuple-like formである。

`F A -> B`は`(F A) -> B`である。`F A->B`ではnested ML argumentがarrowを所有し、
`F (A -> B)`となる。

## 7. 構成

[syntax content model](../conventions/syntax-content-model.md)、[Rowan CST
notation](../conventions/rowan-cst.md)、[recovery `Error` and `Invalid`
topology](../conventions/recovery-error-invalid-topology.md)は共有する`syntax-v0`の
表記とrecovery factを定める。named record、`forall`、effect row、polymorphic
variant、bracket rowの各ページは、ここで定めるprimary/arrow positionを拡張する。

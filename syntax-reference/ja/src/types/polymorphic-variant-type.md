# Polymorphic-variant type

## 1. 正本と対象範囲

このページは`syntax-v0`の`PolymorphicVariantType`を定める。2026年8月20日の
Authoritative polymorphic-variant section、polymorphic-variant current-Item
recovery authority、structured `Invalid` topology authorityに従う。2026年9月10日の
polymorphic-variant foreign-close slot authorityはforeign-close wrapperを定める。

type-only formの`:{A Int, B}`、tag/payload boundary、recoveryを対象とする。
expression/pattern variant、type semantics、lowering、inference、diagnostic wordingは
対象外である。

## 2. 受理構文

```text
PolymorphicVariantType := ":" adjacent "{" G* [ PolymorphicVariantTag { PolyVariantTagBoundary PolymorphicVariantTag } [ PolyVariantTagBoundary ] ] "}"
PolymorphicVariantTag := Identifier { PolymorphicVariantPayload }
PolymorphicVariantPayload := nonempty same-line trivia TypeExpressionInTypeMlScope
PolyVariantTagBoundary := comma | qualifying newline
```

`{`はcolon endから正確に始まる。physical newlineはtagのinner payload sequenceを終える。
qualifying newlineをtag boundaryとしてclassifyできるのはouter tag listだけである。

## 3. 受理と境界

canonical primary judgeはactive stop/caller-owned closeを返した後、ordinary name/number/`(`/`{`
より先に`for`、adjacent `"'["`、adjacent `":{"`をprobeする。bare `:`はcommitしない。
`:{A}`はvariant primaryだが、`: {A}`、`:/*c*/{A}`、`:\n{A}`は受理しない。

admission後、outer brace/list ownerがtag/close recoveryを所有する。tag内のsame-line payload
candidateはType-ML scopeのsiblingであり、互いのTypeApply tailではない。complete variantは
ordinary tail judgeへ戻るため、`F :{A}`はapply argumentとなる。

## 4. Direct Rowan CST

`PolymorphicVariantType`はcolon、brace、direct `PolymorphicVariantTag`、comma、trivia、
closeをsource orderで持つ。各tagはnameとdirect `PolymorphicVariantPayload`を持つ。各payload
はboundary triviaとdirect `TypeExpression`を持つ。

wrong-kind tag-name recoveryは、このownerだけに定めたstructured `Invalid` topologyを使う。
`PolymorphicVariantForeignClose`はlocally consumed foreign close一つとそのraw `Error`
groupをwrapする。item error、tag-separator error、accepted punctuation、trivia、`Missing`、
retry source、`Invalid`のwrapperではない。tag-separator errorはseparator slotのdirect raw
groupのままであり、foreign-close wrapperを使わない。

wrong-kind Type-shaped tag nameは、このownerだけに定めたstructured `Invalid` topologyを
使う。malformed non-NUD tagはraw `Error` groupのままである。synthetic inner payload-list
wrapperは作らない。

## 5. Recovery CST

non-adjacent/incomplete `:{` introducerにはvariant authorityがない。leading/repeated commaは
tag-slot `Missing`となる。real trailing commaはempty tagなしに保持する。non-caller-owned
semicolonはtag-separator raw `Error`となりouter tag judgeへ戻る。

wrong-kind Type-shaped tag nameはvariantのstructured `Invalid` recoveryを使い、同じtag
slotをretryする。malformed non-NUD tagはそのslotのraw `Error` groupとなる。missing payload
boundary/malformed payloadはpayload slotでrecoverする。locally consumed foreign closeごとに
`PolymorphicVariantForeignClose` wrapper一つを置く。ほかのmissing/mismatched braceはclose
slotでrecoverし、caller-owned boundaryは消費しない。

## 6. Source/CST例

`:{A Int, B}`はtag `A`と`B`を持ち、`A`はdirect payload一つを持つ。`:{A Int Bool}`では
`A`の下にpayload sibling二つがあり、`Bool`は`Int`のTypeApply tailではない。

```text
:{A Int
B}
```

newlineはinner payload sequenceではなくouter tag-list boundaryに属する。

## 7. 構成

[Standalone `TypeExpression` core](type-expression-core.md)がpayload typeとこのprimary後の
ordinary tailを定める。[syntax content model](../conventions/syntax-content-model.md)、
[Rowan CST notation](../conventions/rowan-cst.md)、[recovery `Error` and `Invalid`
topology](../conventions/recovery-error-invalid-topology.md)は共有する`syntax-v0`規約を
定める。

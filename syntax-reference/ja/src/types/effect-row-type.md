# Effect-row type

## 1. 正本と対象範囲

このページは`syntax-v0`の`EffectRowType`を定める。2026年8月20日のAuthoritative
effect-row section、Parenthesized/EffectRow current-Item recovery authority、
type-delimited foreign-close topology authorityに従う。

adjacent apostrophe-bracket type primaryとdelimited itemを対象とする。row-tail meaning、
open/closed row classification、effect inference、lowering、diagnostic wordingは対象外である。

## 2. 受理構文

```text
EffectRowType := "'" adjacent "[" G* [ TypeExpression { EffectRowDelimiter TypeExpression } [ EffectRowDelimiter ] ] "]"
EffectRowDelimiter := comma | semicolon | qualifying newline
```

apostropheと`[`はadjacentである。opening triviaがlayout baseを定める。
equal-or-shallower newlineはitemを区切り、deeper newlineはcurrent itemをcontinuationする。

## 3. 受理と境界

active stop/close/canonical NUD `for`の後、primary judgeはordinary type nameより先にcomplete
adjacent `"'["` introducerをprobeする。`'e`はsigil identifierのままであり、`' [`と
`'/*c*/[e]`はeffect rowを受理しない。

accepted rowはbracket delimiter、item、separator、layout、matching closeを所有する。その後は
ordinary tail judgeへ戻るため、`'[e]::Result`、`Foo '[e]`、`'[e] -> Out`はpath、apply、
arrowとしてcompositionする。

## 4. Direct Rowan CST

`EffectRowType`はapostrophe、bracket、trivia、literal separator、direct
`TypeExpression` itemをsource orderで持つ。item-list、row-tail、open/closed-row wrapperは
作らない。newline separatorはtriviaのままである。

locally consumed mismatched closeには`TypeDelimitedForeignClose`を使い、そのmaximal raw
`Error` groupだけを含める。このnodeは`EffectRowType`または`ParenthesizedTypeGroup`の下で
だけemitし、trivia、`Missing`、accepted punctuation、retry source、`Invalid`を含まない。

## 5. Recovery CST

absent item/separator/closeはslot-local `Missing`となり、malformed sourceはそのslotのraw
`Error` groupとなる。current applyをcontinuationできないsame-line next itemはmissing
separatorをrecoverしてitemをretryする。real `]`前のtrailing separatorはvalidでありempty
itemを作らない。

EOF/protected outer boundary前のseparatorではmissing item/close slotを分ける。matching `]`
はlocalであり、protected caller/outer closeは消費しない。locally consumed mismatched close
だけが`TypeDelimitedForeignClose`を使う。

## 6. Source/CST例

`'[]`はintroducerとbracketだけを持つ。`'[e]`はdirect `TypeExpression` item一つを持つ。
`'[tick; 'effect]`はitem二つとliteral semicolon separatorを持つ。semicolonはrow-tail
interpretationではない。`Foo '[e] -> Out`は`Foo`へeffect-row primaryをapplyし、その後に
ordinary arrow tailを持つ。

## 7. 構成

[Standalone `TypeExpression` core](type-expression-core.md)がitemとrow後のtail behaviorを
定める。[syntax content model](../conventions/syntax-content-model.md)、[Rowan CST
notation](../conventions/rowan-cst.md)、[recovery `Error` and `Invalid`
topology](../conventions/recovery-error-invalid-topology.md)は共有する`syntax-v0`規約を
定める。

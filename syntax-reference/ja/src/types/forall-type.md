# `forall` type

## 1. 正本と対象範囲

このページは`syntax-v0`の`ForallType`を定める。2026年8月20日のAuthoritative
`forall` sectionと`forall` current-Item recovery authorityに従う。

contextual type-primary spellingの`for 'a 'b: T`、binder、body、bounded layout、
recoveryを対象とする。statement `for`、non-apostrophe binder、type meaning、lowering、
diagnostic wordingは対象外である。

## 2. 受理構文

```text
ForallType := "for" ForallTypeBinder { ForallTypeBinder } ForallColonTrivia ":" ForallBodyTrivia TypeExpression
ForallTypeBinder := ForallBinderBoundary ApostropheTypeBinderName
ForallBinderBoundary := nonempty same-line trivia | deeper continuation trivia
ApostropheTypeBinderName := "'" UnicodeIdentifierBody
```

layout baseはaccepted `for`の直後に取る。binder boundaryはnonemptyである。colon/body
gapはemptyでもよい。equal-or-shallower newlineはforall-owned triviaにならない。

## 3. 受理と境界

canonical type NUD positionではexact maximal `for`がidentifierより先に`ForallType`を
受理する。`forx`、`forall`、`for_`はidentifierのままである。TypeApply LED positionの
`for`はforallではなくordinary identifier seedとなる。

binder前はapostrophe binderまたは`:`だけがprogressを作る。binder後はapostropheが次の
binderを開始し、non-binder primaryはmissing colon後にbodyとしてretryする。bodyはpath、
call、apply、arrowを所有する。raw forallはterminalなのでouter tailにはgroupingが要る。

## 4. Direct Rowan CST

`ForallType`は`ForKw`、direct `ForallTypeBinder`、colon-side trivia、`Colon`、body
trivia、direct body `TypeExpression`をsource orderで持つ。各binderはboundary triviaと
apostrophe nameを持つ。delimiter/list/synthetic separator nodeは作らない。

## 5. Recovery CST

first missing binderはbinder-slot `Missing`一つとなりcolon/bodyへcascadeしない。adjacent
binderはmissing binder boundaryを作り同位置でbinderをretryする。accepted binder後の
EOF/protected boundaryはmissing colonだけとなる。non-binder primaryはmissing colon後に
bodyをretryする。

malformed binder、colon-side continuation、bodyはselected slotのraw `Error` groupとなる。
accepted colon後のmissing/malformed bodyはbody slotに残る。comma/semicolonはbinder
separatorではなく、protected stop/close/caller boundary/qualifying newlineは消費しない。

## 6. Source/CST例

`for 'a: A -> A`はdirect `ForallTypeBinder`一つを持ち、bodyがarrow tailを持つ。

```text
for
  'a
  'b:
    Pair('a, 'b)
```

各binderがleading continuation boundaryを所有し、deeper colon-to-body triviaは
`ForallType`に属する。`(for 'a: 'a)::Result`はforallをgroupしてからpath tailを付ける。

## 7. 構成

[Standalone `TypeExpression` core](type-expression-core.md)がrecursive body grammarを
定める。[syntax content model](../conventions/syntax-content-model.md)、[Rowan CST
notation](../conventions/rowan-cst.md)、[recovery `Error` and `Invalid`
topology](../conventions/recovery-error-invalid-topology.md)は共有する`syntax-v0`規約を
定める。

# Named-record type

## 1. 正本と対象範囲

このページは`syntax-v0`の`NamedRecordType`を定める。2026年8月20日の
Authoritative named-record section、record-field/record-sequence current-Item
recovery record、named-record slot authorityに従う。

`{a: A, b: B}`のtype primary、field、separator、close、recoveryを対象とする。
record pattern/expression、field semantics、type checking、lowering、diagnostic wordingは
対象外である。

## 2. 受理構文

```text
TypePrimary := ... | NamedRecordType
NamedRecordType := "{" G* [ TypeRecordField { RecordTypeSeparator TypeRecordField } [ RecordTypeSeparator ] ] "}"
TypeRecordField := Identifier TypeRecordFieldTrivia ":" TypeRecordFieldTrivia TypeExpression
RecordTypeSeparator := comma | qualifying newline
TypeRecordFieldTrivia := empty | same-line trivia | deeper continuation trivia
```

opening triviaがlayout baseを定める。equal-or-shallower newlineはseparator judgmentへ
戻り、deeper newlineはfield RHSをcontinuationする。semicolon、shorthand、default、
spread、sigil/numeric/path-qualified nameはfield syntaxではない。

## 3. 受理と境界

required type-primary positionの`{`はnamed recordを受理してそのownerへcommitする。
`F {a: A}`はapply argumentであり、adjacent `F{a: A}`にはapply authorityがない。

plain identifierだけがfieldを開始する。recordはfield colon、comma、layout、matching
closeを所有する。RHSがwhitespace applyを消費する前に、field-sequence judgeはcomplete
`Identifier ... :` headを認識する。missing record separatorをrecoverしてそのfieldを
retryし、次fieldを前のRHS applyにはしない。caller boundaryとouter closeは消費しない。

## 4. Direct Rowan CST

`NamedRecordType`はbrace、trivia、direct `TypeRecordField`、accepted commaをsource
orderで持つ。`TypeRecordField`はname、colon、trivia、direct `TypeExpression` RHSを
source orderで持つ。qualifying newline separatorはtriviaのままである。

`NamedRecordTypeSeparator`はexisting separatorの`Missing`またはraw `Error`だけを
含む。`NamedRecordTypeClose`はnative triviaとraw errorの後に`}`または`Missing`を置く。

```text
NamedRecordTypeClose := NativeTrivia* ( Error NativeTrivia* )* ( "}" | Missing )
```

committed recordごとに`NamedRecordTypeClose` wrapperは一つである。これらのwrapperに
独立diagnosticはなく、accepted comma/whole fieldをwrapしない。

## 5. Recovery CST

absent field/name/colon/RHS/separator/closeはslot-local `Missing`一つとなり、そのslotの
malformed sourceはraw `Error` groupとなる。same-line complete next field headは
separator `Missing`を作り同位置でfieldをretryする。semicolonはseparator recoveryであり
field separatorではない。

field recoveryとsequence recoveryは別である。pending whole-field `Missing`は同じbyte
coordinateでもclose nodeより前に置く。matching closeはlocalである。close recoveryがcommit
後はnative trivia、raw error、最後の`}`または`Missing`をその一つのclose wrapperに
残す。
protected caller boundary/outer closeはrecord外に残り、
spread/shorthand/default/`Invalid` nodeを作らない。

## 6. Source/CST例

`{a: A, b: List(Int)}`はdirect `TypeRecordField`二つを持ち、二つ目のRHSには
`TypeCallTail`がある。

```text
{
  a: A
  b: B
}
```

このnewlineとindentationはsource-bearing record childでありsynthetic separatorではない。
`F {a: A}`はprimaryが`NamedRecordType`の`TypeApplyArgument`を持つ。

## 7. 構成

[Standalone `TypeExpression` core](type-expression-core.md)はRHSと周囲のapply behaviorを
定める。[syntax content model](../conventions/syntax-content-model.md)、[Rowan CST
notation](../conventions/rowan-cst.md)、[recovery `Error` and `Invalid`
topology](../conventions/recovery-error-invalid-topology.md)は共有する`syntax-v0`規約を
定める。

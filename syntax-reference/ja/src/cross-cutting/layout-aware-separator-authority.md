# Layout-aware separator authority

## 対象範囲

この規則は、`ParenthesizedExpression`、`ParenthesizedPattern`、`ListPattern`、`RecordPattern`、および外側の列ownerを持たないinline colon argumentのcommaまたはnewlineによる境界を定める。
completeなitemの後のtriviaが次のitemを区切るか、現在のitemを継続するかを決める。

この規則はsemicolonを共通separatorとして追加しない。
item grammar、literal trailing commaの意味、matching closeの所有権、statementとarmの境界も変更しない。

## 境界規則

各delimited sequenceは、最初のitemより前にopenerでlayout baseをcaptureする。
opener後のtriviaがphysical newlineを含み、最後のphysical newlineの次のindentationがincoming baselineより深い場合は、そのindentationをbaseとする。
それ以外の場合はincoming baselineをbaseとする。

```text
DelimitedSeparator := ExplicitCommaBoundary
                    | ImplicitNewlineBoundary(base)

ImplicitNewlineBoundary(base) :=
    maximal trivia containing a physical newline
    whose following-line indentation <= base
```

completeなitemの後ではexplicit commaが先に勝つ。
commaがなければ、qualifying newlineが境界となる。
deeper newlineは現在のitemのcontinuation triviaとして残る。
どちらのseparatorもなく、同じ行で次のitemが始まる場合、recoveryはその位置にmissing separatorを置く。

inline colon applicationでは、visibleなouter sequence ownerがcommaとqualifying newlineの両方を所有する。
この場合、colon RHSはちょうど1個のargumentを持つ。
そのownerがなければ、colon applicationは最初のargumentが始まった後のcommaとqualifying-newline boundaryを所有する。

## Rowan CSTのsource order

explicit commaはsequence ownerのsource-bearing comma tokenとなる。
implicit newlineはseparator token、`Missing(Comma)`、separator nodeを追加しない。
newline、space、commentは、completeなitemと次のitemまたはcloseの間に、containerのordinary triviaとしてsource順に残る。

この規則はCST nodeを追加しない。
literal trailing commaの意味はliteralのままである。
trailing implicit newlineは有効な終端だが、trailing commaではない。

## Recoveryとhandoff

item間またはlocal closeの直前にあるqualifying newlineは有効であり、recovery structureを作らない。
deeper newlineは現在のitemへ返す。
sequenceは、後続のtextを新しいitemへ昇格してはならない。
commaのないsame-line next itemは、zero-widthのmissing separatorを一つ受け取り、同じsource positionでretryする。

outer ownerがすでにgapをclaimするとき、この規則はgapをconsumeしない。
たとえば、[ambient statement-owner boundary](ambient-statement-owner-boundary.md)は、strict statement dedentまたは`else`/`elsif` companionを外側のstatement contextに残せる。

## 例

| Source | 結果 |
| --- | --- |
| `()` | 空のparenthesized sequence。 |
| `(a,)` | literal trailing commaを持つ1個のitem。 |
| `(\n  a\n  b\n)` | base indentationは`2`。itemは2個で、最後のnewlineは有効な終端。 |
| `(a\nb)`、base `0` | qualifying newlineで区切られた2個のitem。 |
| `(a\n  b)`、base `0` | deeper newlineは最初のitemを継続する。`b`は2個目のitemではない。 |
| `(f: a, b)` | parenthesized sequenceがcommaを所有するため、colon RHSは1個のargumentを持つ。 |

## 組み合わせと制限

各construct pageは、opener、item grammar、close、construct固有のrecoveryを定める。
このページが与えるのは共有するnewline classificationだけである。
malformed TypeExpressionのnewline recoveryは定めない。
[TMN](tmn-malformed-newline-owner-policy.md)を参照する。
local gapを取り得るambient statement ownerのcaseも定めない。

正本は、[syntax architecture design](../../../notes/design/2026-08-20-yu-syntax-chasa-architecture.md)のAuthoritativeな*layout-aware comma-or-newline delimited sequence authority*（9314–9693行）である。

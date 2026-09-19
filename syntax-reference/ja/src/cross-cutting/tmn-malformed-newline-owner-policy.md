# TypeExpression malformed-newline owner policy (TMN)

## 対象範囲

TMNは、nonemptyなmalformed TypeExpression prefixの後のphysical newlineをどのownerへ属させるかを決める。
required type slot、path segment、arrow right-hand side、`Call`、`Parenthesized`、`EffectRow`が所有するdelimited type item、`forall` phase、NamedRecord type fieldに適用する。
polymorphic variantとincompleteなNamedRecord field-name phaseの明示的なhandoffも定める。

TMNは受理するTypeExpression grammar、type precedence、delimiter ownership、diagnostic wordingを変更しない。
recovery triviaだけを分類する。
`BracketRow`は`BracketRowAlignmentPolicy`と`BR-RP1`を保ち、generic TMNを使わない。

## Newlineの所有権

continuation-qualifiedなrecovery slotは、slotの開始時にcontinuation baseをcaptureする。
newline後のindentationがcaptureしたbaseより深い場合だけ、newlineはそのslotを継続する。

```text
continues_after_newline(trivia, base) :=
    trivia contains a physical newline
    and following-line indentation > base
```

activeなcaller newlineは、すべてのTMN policyとindentation comparisonより先に勝つ。
それ以外では、continuation-qualified slotはequal-or-shallower newlineをowner boundary、deeper newlineをsame-slot continuationとして扱う。
explicitなany-physical handoff policyはすべてのphysical newlineで返す。
これはpolymorphic variant recoveryを含め、内側のphaseが後続を安全に判定できない位置で使う。

Pattern annotationのouter required type entryは、そのPatternがcaptureしたcontinuation baseを使う。
nested type recoveryは通常のactive type baseを使う。

## Rowan CSTのsource order

TMNはsource syntaxやCST nodeを追加しない。
malformed source fragmentは、文書化されたgrammar slotの`Error` tokenとして残る。
同じslotが継続する場合、保持したtriviaはその`Error` tokenとretryしたtype childの間にsource順で一度だけ現れる。
TMNがboundaryを返す場合、malformedな`Error`はtriviaの前で終わる。
enclosing ownerがtriviaとfollowing boundaryを保持する。

`Missing`、`Error`、`Invalid`には共有の[recovery topology](../conventions/recovery-error-invalid-topology.md)を使う。
TMNは新しいstructured recovery ownerを許可しない。

## Recoveryとhandoff

| 結果 | 所有権 |
| --- | --- |
| 現在位置でretry | valid retry candidateをsame required slotのために未消費で残す。 |
| deeper triviaの後でretry | same slotがexactなtriviaを一度consumeしてcandidateをretryする。 |
| 現在位置のboundary | 現在のbyteをboundaryを認識するownerに残す。 |
| triviaの後のboundary | malformedな`Error`はtriviaの前で終わる。enclosing ownerがtriviaとfollowing boundaryをconsumeする。 |

any-physical handoffも、candidate-completeなouter ownerへnewline triviaを未消費で残す。
handoffまたはboundaryは、malformedな`Error`の後に同じ原因の`Missing`を追加してはならない。

## 例

| Source | 結果 |
| --- | --- |
| `x: @\n  Int` | deeper newlineは、同じrequired annotation type slotで`Int`をretryする。`Error`は`@`だけを含む。 |
| `A::@\n  B` | deeper newlineは、同じpath segmentとして`B`をretryする。 |
| `T(@\n  A)` | deeper newlineはcall itemとして`A`をretryする。callが`)`を所有する。 |
| `x: @\n  <EOF>` | `Error`は`@`だけを含む。outer ownerがtriviaを受け取り、同じ原因の`Missing`は追加しない。 |
| `:{@\n  B}` | polymorphic-variantのinner phaseはphysical newlineでhandoffする。`B`を自身のcontinuationとしてclaimしない。 |

## 組み合わせと制限

TMNはmalformed-newline resultを与える。
owning constructは、local close、separator、active stop、recovery slotを引き続き決める。
nested TypeExpressionを越えてcaller-owned newlineを保つ場合は、[positional-fence rule](positional-fence.md)に従う。
complete itemのlayout separatorには、[layout-aware separator authority](layout-aware-separator-authority.md)を使う。TMNは使わない。

正本は、[syntax architecture design](../../../notes/design/2026-08-20-yu-syntax-chasa-architecture.md)のAuthoritativeな*TypeExpression malformed recovery newline owner policy*（16557–16860行）である。

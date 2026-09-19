# Ambient statement-owner boundary (ASOB)

## 対象範囲

ASOBは、nested local sequenceまたはcontinuationにcloseがない場合の、statement contextにある二つのcollisionを解決する。

- nearest visible statement baselineよりstrictly shallowなphysical newline。
- visibleな`IfExpression`のexactな`else`または`elsif` companion。

どちらの場合も、local item、field、continuationがgapをconsumeする前にambient statement ownerがoriginal gapを取る。
ASOBは、[ASOB participation and precedence](asob-integration-matrix.md)に挙げるconstruct familyのcompletedまたはrecovered continuation pointに適用する。

ordinary same-indent statement candidate、braced current-depth statement boundary、caseまたはcatch arm boundary、`if`、`where`、`->`、`=`のようなほかのcontextual introducerは解決しない。

## 所有権と優先順位

completeまたはrecoveredなlocal continuation gapでは、次の順序を使う。

1. actual matching own closeまたは既存のcaller-owned fixed delimiter stop。
2. locally allowed explicit separator。
3. ASOB claim。
4. constructが既に持つlocal continuation、layout、retry rule。

ASOB claimには、nearest visible statement baselineからのstrict dedent、またはvisibleな`IfExpression` companionが必要である。
braced statement bodyの内側では、outer statement baselineとouter If companionを隠す。
そのbraced bodyの内側で開始したIf companionはvisibleのままである。

If expressionは、同じIf expressionに属するcompanionだけをconsumeする。
nested If expressionはouter companionを未変更で返さなければならない。

## Rowan CSTのsource order

ASOBはsource syntax、token、Rowan nodeを追加しない。
ASOBがgapをclaimする場合、local constructはoriginal triviaとboundary textを未消費で残す。
ambient ownerが既存のsource-bearing leafをsource順で保持する。

ASOBはrejected implicit boundaryにseparatorも作らない。
各constructのclose slotとitem slotにすでに割り当てたrecovery shapeを保つ。

## Recoveryとhandoff

ASOBがbare implicit candidateをvetoする場合、local ownerはnext itemまたはfield slotを開かない。
そのためmissing itemまたはfieldを追加しない。
acceptedかつunclosedなdelimiterはそれぞれ、own close slotに既存のzero-width `Missing`を実現する。

explicit separatorの後、またはlocal implicit separatorをすでにcommitした後は、通常のlocal next-slot recoveryを使い続ける。
その後のboundaryにあるASOB claimは、commit済みのlocal recoveryを消さない。

local ownerはimplicit-newline gapをconsumeする前にASOBを判定する。
newlineをconsumeした後にfollowing positionからownershipを再判定してはならない。

## 例

| Source | 結果 |
| --- | --- |
| `if condition:\n  struct S { x: Int\nelse: 0` | Structはdedentと`else`をIf expressionへ残す。missing `}`を一つ保ち、missing fieldは追加しない。 |
| `if condition: f(x else: 0` | callは`else: 0`をIf expressionへ残す。missing `)`を一つ保ち、missing argumentは追加しない。 |
| `if condition:\n  { else: 0 }\nelse: 1` | braced bodyはbrace内でouter companionを見せない。outer `else: 1`はIf companionのまま。 |
| `if condition:\n  my [x\nelse: 0` | ListPatternはcompanionをouter If expressionへ残す。missing `]`を一つ保ち、missing pattern itemは追加しない。 |
| `struct S { x: Int,` | explicit commaがlocal authorityを保つ。既存のmissing-fieldとmissing-close recoveryを使う。 |

## 組み合わせと制限

ASOBはcaller-boundary layerである。
[layout-aware separator authority](layout-aware-separator-authority.md)のlocal newline test、[TMN](tmn-malformed-newline-owner-policy.md)のmalformed TypeExpression newline ownership、construct固有のclose ruleを置き換えない。
別のcaller-boundary classへ拡張するには、local syntaxに対する優先順位を定める別のauthorityが必要である。

正本は、[syntax architecture design](../../../notes/design/2026-08-20-yu-syntax-chasa-architecture.md)のAuthoritativeな*ambient statement-owner boundary and layout-delimited implicit-newline collision authority*（18358–19160行）である。

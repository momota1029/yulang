# TypeExpression malformed caller-boundary fence

## 対象範囲

この規則は、nested TypeExpression recoveryが戻る間、TMNが選んだcaller-owned newlineを保つ。
TMNがuntouched maximal trivia runをcaller boundaryに分類した後だけに適用する。
source syntax、追加のtype form、新しいrecovery nodeではない。

## Boundaryを保つ規則

TMNがcaller boundaryを返した後、そのuntouched triviaのexactな開始位置をfenceとする。
parseがその位置にある間、nested TypeExpression ownerはtriviaをconsumeしてはならない。
triviaを越えてclassificationしたり、local closeをconsumeしたりしてもならない。
enclosing callerがtrivia run全体とfollowing boundaryを受け取る。

通常のmultiline layoutはfenceを作らない。
TMNがすでにcaller ownershipを選んだnewlineだけを保護する。
これにより、通常のlocal sequence boundaryとmalformed-recovery handoffを区別する。

## Rowan CSTのsource order

fenceはsource-bearing leaf、structural node、`Missing` nodeを作らない。
既存のsource orderを保つ。
malformedな`Error` tokenはfenced triviaの前で終わり、callerが後でそのtriviaとboundaryを所有する。

fenced boundaryによってacceptedなdelimited constructがunclosedになる場合、そのconstructはown close slotに対する文書化済みのzero-width `Missing`を保つ。
nested accepted constructが一つのclose recoveryを共有することはない。
unclosed instanceごとにown close slotを一度実現する。

## Recoveryとhandoff

fenceはmalformedな`Error`のrangeを変えず、handoffをretryにも変えない。
nested ownerがprotected gapをconsumeすることを防ぎ、callerが次のboundary decisionを行えるようにする。
一つのconstruct instanceは同じgapに対してduplicateなclose `Missing`を作ってはならない。
別のnested instanceは別々のrecovery ownerのままである。

recovery branchをabandonする場合、fenceもそのbranchとともにabandonする。
callerが指定されたtriviaをconsumeした後、fenceは効果を持たない。

## 例

| Source | 結果 |
| --- | --- |
| caller-owned newline下の`T((@ \n  A))` | inner `ParenthesizedTypeGroup`とouter `TypeCall`/`Call`は別々のclose ownerであり、それぞれmissing closeを一つ保つ。newlineと`A`はcaller-ownedのまま。 |
| caller-owned newline下の`{@ \n  a: A}` | malformed fieldは`Error`を持つ。unclosed NamedRecordはmissing closeを一つ保つ。runはcaller-ownedのまま。 |
| caller-owned newlineでない`A::@ \n  B` | fenceは作られない。TMNがdeeper triviaの後で`B`をretryする。 |
| `T(A\n  B)` | malformed recoveryがないためfenceは作られず、通常のlayout handlingを行う。 |

## 組み合わせと制限

malformed newlineがcaller-ownedかを決めるのはTMNだけである。
fenceはnested TypeExpressionを越えてその結果を保つ。
delimiter、stop、layout ruleを置き換えない。
classificationは[TMN](tmn-malformed-newline-owner-policy.md)、`Error`と`Missing`は[recovery topology](../conventions/recovery-error-invalid-topology.md)を参照する。

正本は、`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`のAuthoritativeな*TypeExpression malformed caller boundary positional fence*（16862–17289行）である。

# 関連型糖衣が導入する変数と宣言検査

状態: T13の未接続箇所を具体化した質問。2026-11-10、I-13。
既に承認された糖衣自体や、普通のwhere-only変数の扱いを再質問しない。

spec/06-roles.md 6.3の確定した例:

```yulang
impl Wrap (list 'a) where Container 'a:
    type out = list 'a::item
// 糖衣を展開すると
impl Wrap(list 'a, out = list 'b) where Container('a, item = 'b)
```

6.3は、名前なしの引数が決まれば名前つきの引数の制約が決まり、右辺が生成する
子もPaterson条件の対象にする、としている。同時に、具体的な条件と
HeadDeterminesAssociatedとの関係、参照の循環を残る設計課題にしている。
I-8は、子の関連等式で決まる `'b` までHeadDeterminesAssociatedを広げるよう求める。

現 `CommonRoleStablePaterson.Declaration` は一種類の `List Form` に引数を置き、
名前つき/名前なしの区別、関連型出力のdependency、糖衣由来のbinder情報を持たない。
`CommonRoleIntervalCandidates.namesBound` は全where名がhead capture済みであることを要求する。
したがって、新しい生成側がこの区別を消して既存checkerへ渡すだけでは、
承認済みの糖衣を受理できることも、意味保存/停止もまだ示せない。

対比する普通のwhere-only変数の概形（parser/実機未検証）:

```yulang
impl Parent (box 'a) where Child 'b
```

等式で決まらない `'b` は、6.3の「where中の各変数の出現回数がheadを超えない」で
既に排除される。これを許す提案ではない。上の糖衣では、名前つき出力に現れる
生成binderの出現を、元のhead検査・子検査・決定性へどう対応させるかが未接続である。

1. **遅延案（推奨）**: B4の既存断片はそのまま。名前なしhead、名前つき等式、
   新しいbinder、関連型dependencyを保持するsource宣言を先に設計し、
   承認済み例と6.3の二条件・決定性を同時に満たす検査案を別ノートで提示する。
   今回の既存scannerのoutsideを言語拒否としない。
2. 名前つき引数も含めた糖衣展開後のhead/child全体でサイズと出現回数を数える。
   その上で、名前なし引数から子の関連等式を通した決定性を別に証明する。
   この数え方が6.3の意図を保存し、循環を通さないことは未証明なので採用しない。
3. 関連等式のdependency検査を先に行い、決まる生成binderを明示した後に
   Patersonの比較へ翻訳する。どのbinderをどう数えるか、関連型参照の循環で
   何を拒否するかを別途確定する必要がある。恣意的にサイズ0にはしない。

2/3の受理範囲が変わる場合はユーザー判断が必要。既存意味論を変えずに同じ結果へ
導ける場合は実装・証明の問題として進める。今回はspecやcheckerを変更していない。

関連: [台帳](../design/2026-11-10-boundary-inputs-ledger.md)、
[HeadDeterminesAssociatedの既存判断](2026-11-07-b4-associated-head-recovery.md)。

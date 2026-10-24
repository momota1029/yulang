# 共起分析と保護解除の関係

Date: 2026-10-24
Status: Authoritative for the direct clarification below; the preservation proof and full source correspondence remain obligations
Selected-by: user, directly in the continuing semantics/soundness conversation
Scope: the interpretation of shared effect variables and grouped release targets
Supersedes: the premise that multiple ingress occurrences of `'e?` require a new choice between all-input and selected-input semantics
Implementation: excluded from the current task

## 直接の訂正

ユーザーの発言をそのまま記録する。

> `'e?`そのものを意味論にするわけではなかったんですが，動作原理からすると「実行前にいれる引数が保護され，それが『全く同じ共変位置に出てくる』ときのみ同じ変数になるわけで，『まぜこぜにして解除の対象にする』としても問題は出ない」ことになります．これは共起分析のお陰ですね．別途証明は必要ですが，これは問題ですらない，というのが私の答えです．

順序は、引数の保護という動作原理、共変位置での共起分析、同じ変数による表示、その表示に対応する解除、である。`'e?` の表記を出発点に独立した実行規則を選ぶのではない。共起分析が同じ変数へまとめる対象について、複数入力を解除対象にまとめることを未決定の仕様選択として扱わない。

この発言は、原稿に置いた `A_all` という任意の具体化を選択した回答ではない。表記上同じ binder であることだけを根拠に対象を集める候補が、上の動作原理と共起分析に対応するかは、証明する側の責任である。質問者の提示した「全入力か、指定入力か」の選択肢は撤回する。

## 証明へ引き継ぐ内容

示す対象は、保護された引数の寄与を共起分析によってまとめる前後で、対応する出力位置における保護・解除の観測が一致することである。まず「全く同じ共変位置」を位置の集合の一致として定式化し、同じ集合を持つ成分の併合と解除が両立することを示す。次に、その位置と併合が実際の生成・簡約・一般化・使用に対応することを示す。

効果変数の併合と、動的な受領 receipt・receiver・経路・独立した保護 scope の同一視は区別する。[compose の決定](2026-10-15-compose-scoped-effect-release.md)で要求された独立した保護と寄与の保存を引き続き満たす必要がある。今回の訂正は、行の解が等しいだけの成分を無条件で併合する規則や、別の寄与の保護を消去する規則を追加しない。

「別途証明は必要」という区別を維持する。仕様選択の質問が解消したことは、共起分析の保存定理、現行 source との対応、型健全性全体の証明完了を意味しない。[後続の証明稿](../theory/2026-10-24-cooccurrence-release-preservation.md)に導出と適用範囲を記す。

## 履歴の読み方

`docs/yulang-source-type-safety-ja.tex` §11、修正機械の simulation 稿、最初の sprint outcome にある「複数入力について返答待ち」「A_all の採用待ち」は、その時点の質問者による整理である。この点は本記録で訂正する。凍結済み候補の数学的定義と当時の査読対象 hash は保持する。候補の全規則を承認済みの言語へ読み替えない。

未追跡の `questions/2026-10-24-release-multiple-ingress/` には原質問と質問者の訂正受領記録を保持する。別会話の回答者による approved-answer を捏造せず、直接発言の規範的な記録は本書に置く。

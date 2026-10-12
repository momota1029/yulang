# Extrusionの発生単位によるintrusion：回答案

Question ID: 2026-10-12-type-value-occurrence-association
Question revision: 1
Draft ID: 2026-10-12-type-value-occurrence-association-answer
Draft revision: 2
Predecessor/history: 未承認のrevision 1をanswer-draft-revision-1.mdに保存。本案はrevision 1の所有規則を置き換える。
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `0e621f549035537e4d3e799c78f79dd9385df350`; original Simple-sub `9bae772624c23b52a93c1b226157e16898b4d9db`
Task/thread locator: この回答用会話。外部識別子・正確な時刻は取得できない。
Governing sources: question revision 1; `notes/design/2026-10-10-parent-copy-scc-intrusion.md`; `notes/design/2026-10-12-intrusion-value-type-association.md`; `notes/design/2026-10-12-value-reference-copied-row-ownership.md`

## ユーザーの発言と解釈

> ちょっと待って．起こったextrusion自体にidを振って，SCC内に両辺が入ったらそのidのextrusionをintrusionするというルールが正しいのではないですか？

回答者は「両辺」が例の持ち出し元の値gと持ち出し先の値fを指すかを確認し、ユーザーは次のように回答した。

> そうですね

この二つの発言は、この回答用会話のユーザーメッセージに由来する。以下は、その意図をextrusionの発生単位の規則としてまとめた回答者の解釈であり、まだ全文の承認ではない。

## 決定案

1. 起こったextrusion自体にIDを付け、その発生に持ち出し元の値、持ち出し先の値、および実際の型変数の親・コピー組を結びつけて保持する。
2. 既承認の値参照グラフで、その発生の元・先の値が同じSCCに属したら、そのIDのextrusionをintrusionする。等しくする対象は、その発生に記録した実際の型変数の親・コピー組である。
3. 質問の例では、元はG（関数g）、先はF（関数f）。その発生に(C,B,+,1)と(D,R,-,1)が対応する。FとGが同じSCCに属するため、C=BとD=Rを課す。
4. 対応はextrusionの発生に保持する。型変数IDだけから恒久的に一つの値の所有者を決めたり、関数の型記述全体に一律の所有規則を追加したりする決定ではない。値参照辺のコピー・追加・付け替えも行わない。fresheningだけをextrusionの発生とみなさない。

## 適用範囲と残る課題

質問revision 1に対する、発生単位での値の両端・型の組の対応とintrusion条件の回答とする。revision 1の回答案は採用しない。

IDの具体的な表現、発生の構成単位、共有・メモ化・再利用・極性別コピーを含む全経路での記録保持、SCC判定の実行方法、および健全性・必要なprincipality・通常の推論進行の証明は後続課題とする。例だけに証明対象を限定しない。値参照グラフと既承認の親・コピー等式操作は維持する。証明完了、コンパイラ実装、F5切替を承認する回答ではない。

## 承認と受け渡し

この全文が回答案revision 2。全文への明示的な承認後に、同じ内容と実際の承認発言を含むapproved-answer.mdを保存する。revision 1の履歴は未承認のまま保持し、承認対象の回答本文に含めない。

Pending status: 未承認。回答者はGitを変更しない。承認後も未ステージ・未コミットのまま残し、質問者が検証・統合する。

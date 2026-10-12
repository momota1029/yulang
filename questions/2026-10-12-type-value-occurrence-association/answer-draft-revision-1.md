# 型の出現と値の対応：回答案

Question ID: 2026-10-12-type-value-occurrence-association
Question revision: 1
Draft ID: 2026-10-12-type-value-occurrence-association-answer
Draft revision: 1
Predecessor/history: none; question predecessor is 2026-10-12-value-reference-copy-content-owner revision 2
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `0e621f549035537e4d3e799c78f79dd9385df350`; original Simple-sub `9bae772624c23b52a93c1b226157e16898b4d9db`
Task/thread locator: this answering conversation; external locator unavailable
Governing source/section: question revision 1, option 2; `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, selected operation and Value-reference laws; `notes/design/2026-10-12-intrusion-value-type-association.md`, Qualification; `notes/design/2026-10-12-value-reference-copied-row-ownership.md`, Decision

## ユーザーの発言

> 2ですね．これは「何由来の型変数か」というものに相当するので……．

出典：この回答用会話の直前のユーザーメッセージ。正確な時刻・外部メッセージ識別子は取得できない。

## 発言の解釈

質問の選択肢2「関数全体の型記述による対応」を選ぶ。「何由来か」は、ここでは、その型の出現がどの関数の型記述に属するかを意味する。引数や結果の値そのものの同一性、型変数の最初の割当箇所、型変数IDだけから一意に定まる所有者を意味すると解釈しない。

## 決定案と適用範囲

1. 関数の完全な推論済み型記述の各部分に現れる型は、その記述が表す関数の値に対応させる。引数・結果の部分もこの対応に含む。
2. 要求された型記述をextrusionによって別の関数の型へコピーするとき、そのコピー内の型の出現は、受け取り先の関数の値に対応させる。元の出現の対応と、コピーした出現の対応を保持する。
3. 質問の例では、元の引数型Bと結果型Rの出現はG（関数g）に、コピーCとDの出現はF（関数f）に対応させる。したがって、実際のextrusion組(C,B)と(D,R)の値の対応は、どちらも(F,G)となる。
4. 既承認の値参照グラフではFとGが同じSCCに属するため、この二組はintrusionの対象となり、C=BおよびD=Rを課す。
5. これは型の出現と値の対応を決める規則であり、値参照辺をコピー・追加・付け替えする規則ではない。Y（仮引数y）やV_R（呼び出し結果）をFまたはGと同一視しない。同じSCCの値に対応する任意の型を一律に等しくせず、保持された実際のextrusion親・コピー組に既承認の条件を適用する。
6. 同じ型座標が複数の記述で共有される場合も、その座標IDだけで対応する値を上書きせず、対象の型の出現とextrusion組について対応を特定する。具体的な表現、共有・捕捉・極性別コピー・fresh useを含む全経路の対応保持、健全性・必要なprincipality・通常の推論進行の証明は、この決定に従う後続の構成・証明課題とする。freshening自体からextrusion親・コピー組を作ることは承認しない。

適用範囲は質問revision 1の型の出現と値の対応規則、および例の二組の判定。値参照グラフ、辺の規則、コピー時の参照辺非継承、既承認のintrusion操作は再決定しない。この回答は証明の完了、具体的なデータ構造、コンパイラ実装、F5切替を承認しない。

## 承認

この全文が回答案revision 1。全文の明示的な承認後に、同じ内容と実際の承認発言を含むapproved-answer.mdを保存する。

Pending status: 回答案は未承認。回答者はGitを変更しない。承認後も回答ファイルは未ステージ・未コミットのまま残し、質問者が対応する質問・回答案・承認済み回答を検証して統合する。確定後の訂正は新しい関連質問と再承認を必要とする。

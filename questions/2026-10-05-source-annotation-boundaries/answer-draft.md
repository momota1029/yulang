# 回答案 ①

Question ID: `source-annotation-boundaries`
Question revision: `q1`
Draft ID: `source-annotation-boundaries-answer`
Draft revision: `d1`
Status: 全文への明示的承認待ち
Predecessor/history: 本質問の先行回答案なし
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s) / Governing source/section: 同じディレクトリの `question.md` q1に記載の基準revisionと出典。未承認の編集は新しい権威として扱わない。
Task/thread locator: unavailable: この会話には安定したmessage/thread locatorが公開されていない。

## 原文と解釈

この回答会話でのユーザー発言：

> ①1 ②1 ③2A

番号の選択として記録する。以下の具体化は回答者の解釈を含み、全文の承認は未取得である。

## 決定案と範囲

1. 選択肢1を採用する。対象は束縛の型注釈、引数の型注釈、式の `as Type` とする。この対象の列挙は回答者による具体化であり、承認対象に含む。
2. 各境界では、その位置の現在のendpointを注釈のtargetと直接比較する。成功後はtargetと局所的なrealization証拠を外側へ渡す。引数では、既存のValue-entry／retained-Computationの役割に従う入口処理を維持し、注釈のtargetをその役割に応じて用いる。
3. 後続の境界は前の境界が渡したendpointを用い、前のrealization証拠を保存したまま自身の証拠を加える。個別の具体比較の成功から、元のendpointと最終targetの直接比較の成功を導かない。
4. ソース境界なしの中間具体適応を認めない。入れ子の境界は各々独立に扱うが、`x as int as str` を二つの境界とする構文変更は選択しない。
5. 対象外の注釈形式、完全なsource adequacy、solver変更、compiler実装、期待出力変更は承認範囲に含めない。

## 承認と引き渡し

承認対象は `source-annotation-boundaries-answer/d1` 全文。明示的承認後、この全文と実際の承認発言を含む `approved-answer.md` を最後に保存する。回答者は回答ファイルのみを書き、Git操作を行わない。未統合の回答は未ステージ・未コミットのまま残し、質問者が検証・統合する。訂正には新しい関連質問と再承認が必要となる。

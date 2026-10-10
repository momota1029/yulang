# Approved answer: contextual-residual-owner

Question ID: `contextual-residual-owner`
Question revision: `q1`
Approved draft ID: `contextual-residual-owner-answer`
Approved draft revision: `a1`
Draft history locator: `answer-draft.md`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): question q1 の baseline `83b22c95369538a3f4c93810f9693500c12c9937`、研究参照 `9610f0c3e`, `4976fde94`, `98d21e1bc`, `c2674ba5a`, `de5c400d6`。設計本文のレビュー対象 SHA-256: `c01281271a94cfcfed83b9aea215098d06ec990507c663f41dbfb9fa59da747b`。現行性は質問者が統合前に再検証する。
Task/thread locator: unavailable; stable conversation identifier and exact message timestamp are not exposed
Governing source/section: `notes/design/2026-10-10-contextual-residual-owner-design.md` §§3–7; `notes/design/2026-10-10-parent-copy-scc-intrusion.md` “Selected operation”; `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1,4

## Exact approved draft content

# 回答案：contextual-residual-owner

Question ID: `contextual-residual-owner`
Question revision: `q1`
Draft ID: `contextual-residual-owner-answer`
Draft revision: `a1`
Status: Pending explicit approval; non-authoritative
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): question q1 の baseline `83b22c95369538a3f4c93810f9693500c12c9937`、研究参照 `9610f0c3e`, `4976fde94`, `98d21e1bc`, `c2674ba5a`, `de5c400d6`。設計本文のレビュー対象 SHA-256: `c01281271a94cfcfed83b9aea215098d06ec990507c663f41dbfb9fa59da747b`。現行性は質問者が統合前に再検証する。
Task/thread locator: unavailable; stable conversation identifier and exact message timestamp are not exposed
Governing source/section: `notes/design/2026-10-10-contextual-residual-owner-design.md` §§3–7; `notes/design/2026-10-10-parent-copy-scc-intrusion.md` “Selected operation”; `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1,4

## ユーザーの原文と出所

この回答会話の直前のユーザーメッセージ:

> ①一旦1で．②参照できないと再帰関数が書けないので1で

## 解釈

「①一旦1で」を、この質問の選択肢1を当面の方針として選ぶ意思と解釈する。将来の自動的な統合や選択肢2への移行は含めない。

## 提案する決定と範囲

選択肢1：残余レシピの同一性には、作成時の経緯（constructor lineage）を保持する。

元の行変数が等しくなったり残余キーが一致したりしても、それだけで別々の残余レシピを統合しない。元の行変数に対する等価化では、適用対象となる現在・将来の下限制約を、保持したすべてのレシピへ伝える。

実際の extrusion の親とコピーが同じ SCC に入り、既存の intrusion 条件を満たした場合は、行変数を等しくする。その際も、すべてのレシピ、フィルター、由来、文脈付きの辺を保持し、必要な制約伝播を行う。

注釈の局所性、正確な文脈観測、complete Call、通常の推論と必要な principality を保つ。正確な伝播、逆方向のフィードバック、capture/freshening、rollback、および受理範囲の成立は、後続の設計・証明・実装検証で確立する。この選択自体でそれらが完了したとは扱わない。

対象は文脈付き残余の同一性方針と、それに依存する具体的エフェクト付き仮引数注釈の後続作業。入力制限、有限の文脈件数上限、資源閾値、拒否境界、診断、注釈の意味変更、F5 切替は承認しない。方針変更には改めて設計と承認が必要。

## 承認と公開

この全文の `a1` への明示承認後に、同じ内容と実際の承認原文を含む `approved-answer.md` を保存する。回答者は Git を変更しない。質問者が現行性と承認を検証し、対応する質問・回答案・承認済み回答を統合する。

## Explicit approval provenance

User approval quote:

> OK

Approval message/thread locator: unavailable; stable conversation identifier and exact message timestamp are not exposed
Approval date/context: 2026-10-10（環境日付）。この回答会話で両方の a1 全文を表示し、「両方のa1を承認」と応答するよう求めた直後のユーザーメッセージ「OK」による両案の承認。
Revision explicitly approved: `contextual-residual-owner-answer/a1`, question `contextual-residual-owner/q1`
Authorized scope: 選択肢1：constructor lineage を残余レシピの同一性として保持し、同一化された元の行から全レシピへ現在・将来の適用対象下限制約を伝播する。既存の同一 SCC 内の親・コピー等価化と全レシピ・フィルター・由来・文脈付き辺を保持する。その他の範囲と未完了義務は以下の承認済み全文のとおり。

Publication: finalized local answer; unstaged and uncommitted. The answering primary performs no Git mutations. The questioning primary validates freshness, identities, exact draft content and approval provenance before integrating the matching question/draft/answer bundle. Publication does not declare implementation completion or waive design/review gates. Finalized draft and answer are immutable; corrections require a new linked question and renewed approval.

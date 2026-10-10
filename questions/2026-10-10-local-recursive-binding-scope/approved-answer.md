# Approved answer: local-recursive-binding-scope

Question ID: `local-recursive-binding-scope`
Question revision: `q1`
Approved draft ID: `local-recursive-binding-scope-answer`
Approved draft revision: `a1`
Draft history locator: `answer-draft.md`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): question q1 の implementation baseline `5daa64d6a`; Oracle reference `a58eefc31e22141574b6f20c6a5748151c6d79f1`。現行性は質問者が統合前に再検証する。
Task/thread locator: unavailable; stable conversation identifier and exact message timestamp are not exposed
Governing source/section: `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` §3; `notes/design/2026-10-10-parent-copy-scc-intrusion.md` “Selected operation”; `notes/progress/2026-10-10-generic-local-source-hir.md` “Implementation”

## Exact approved draft content

# 回答案：local-recursive-binding-scope

Question ID: `local-recursive-binding-scope`
Question revision: `q1`
Draft ID: `local-recursive-binding-scope-answer`
Draft revision: `a1`
Status: Pending explicit approval; non-authoritative
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): question q1 の implementation baseline `5daa64d6a`; Oracle reference `a58eefc31e22141574b6f20c6a5748151c6d79f1`。現行性は質問者が統合前に再検証する。
Task/thread locator: unavailable; stable conversation identifier and exact message timestamp are not exposed
Governing source/section: `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` §3; `notes/design/2026-10-10-parent-copy-scc-intrusion.md` “Selected operation”; `notes/progress/2026-10-10-generic-local-source-hir.md` “Implementation”

## ユーザーの原文と出所

この回答会話の直前のユーザーメッセージ:

> ①一旦1で．②参照できないと再帰関数が書けないので1で

## 解釈

「②参照できないと再帰関数が書けないので1で」を、この質問の選択肢1を選び、単一のローカル関数の自己参照を認める意思と解釈する。

## 提案する決定と範囲

選択肢1：単一のローカル関数の自己再帰をサポートする。定義の初期化式を推論する間から、その束縛名を参照できるようにする。

初期化式は一つの未確定な単相の live root に対して推論し、再帰参照はその同じ root を制約する。初期化式自身の制約がそろった後も、既存の live local root と境界を保持し、後の capture/freshening に用いる。

隣接するローカル束縛の可視性は逐次のままとし、ローカル相互再帰グループと多相再帰は今回の対象に含めない。一般の値の自己初期化、新しい注釈規則も選択しない。

既存の親・コピー間の SCC 等価化、live-let extrusion、注釈の衛生性、complete Call を保持する。HIR の名前解決と同一性形成、solver の処理順序、live scheme への移行、rollback、対象を絞ったソース検証を後続作業で整合させる。この回答は証明・実装・公開移行の完了や F5 切替を宣言しない。

## 承認と公開

この全文の `a1` への明示承認後に、同じ内容と実際の承認原文を含む `approved-answer.md` を保存する。回答者は Git を変更しない。質問者が現行性と承認を検証し、対応する質問・回答案・承認済み回答を統合する。

## Explicit approval provenance

User approval quote:

> OK

Approval message/thread locator: unavailable; stable conversation identifier and exact message timestamp are not exposed
Approval date/context: 2026-10-10（環境日付）。この回答会話で両方の a1 全文を表示し、「両方のa1を承認」と応答するよう求めた直後のユーザーメッセージ「OK」による両案の承認。
Revision explicitly approved: `local-recursive-binding-scope-answer/a1`, question `local-recursive-binding-scope/q1`
Authorized scope: 選択肢1：単一ローカル関数の初期化式で自己参照を認め、再帰参照は同一の未確定な単相 live root を制約する。既存の live root と境界を後続の capture/freshening に保持する。隣接束縛の逐次可視性を保持し、相互再帰グループ・多相再帰を含めない。その他の範囲と未完了義務は以下の承認済み全文のとおり。

Publication: finalized local answer; unstaged and uncommitted. The answering primary performs no Git mutations. The questioning primary validates freshness, identities, exact draft content and approval provenance before integrating the matching question/draft/answer bundle. Publication does not declare implementation completion or waive design/review gates. Finalized draft and answer are immutable; corrections require a new linked question and renewed approval.

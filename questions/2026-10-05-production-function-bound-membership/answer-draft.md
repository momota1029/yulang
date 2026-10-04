# 回答案：production Function-bound membership

Question ID: `production-function-bound-membership`
Question revision: `q1`
Draft ID: `production-function-bound-membership-answer`
Draft revision: `d1`
Status: Pending explicit approval of the complete displayed draft
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `c526291119cb1962713b7e10fe963343f641278b` (question's source baseline)
Task/thread locator: unavailable: this conversation exposes no stable message/thread locator
Governing source/section: `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` Theorem C §§2–4; `notes/design/2026-10-04-source-indexed-callback-realization.md` §§1–4, 7; `notes/design/2026-10-02-source-interface-adequacy-theorem.md` §§2–4

## ユーザーの原文と出典

この回答会話の2026-10-05の選択発言：

> じゃあ2ですね．型推論とはそういうものです．

この発言はOption 2の選択を記録する。以下の回答案全文への承認はまだ取得していない。

## 解釈

型推論では安全な抽象化を許し、各関数のソースから生成される振る舞いを完全に復元・特定することを要求しない、という方針として解釈する。これはユーザーの原文そのものではなく、直前の会話を踏まえた回答者の解釈である。

## 決定案と範囲

1. `q1`のOption 2を選択する。本番のFunction boundは、ポートと必要な型・効果・権限・依存関係の制約に整合する保守的な追加の観測を許せる。各観測がソース構成子の証拠を持つことを、完全なmembershipの必須条件にはしない。
2. 許す追加の観測を網羅的に定めるmembership規則は、後続の設計・証明課題とする。ポートの型が一致するだけで任意の継続、発生元、権限、`nu,K,D`の関係を許す決定ではない。
3. Theorem Cと`P_ref`は、ソース生成の参照解釈についての結果として維持する。本番の完全なboundとの一致や`P_actual ⊆ P_checked`は、この選択だけでは成立したと扱わない。追加の観測を含む全体について、保持する証拠との対応または独立した包含証明が必要である。
4. この回答の範囲は本番の意味付け・証明方針の選択に限る。具体的なmembership規則、実装、構文、parser/HIR API、solver carrier、callback B、不等式solver、既存の効果証拠の変更は承認しない。独立した設計レビューと必要な承認は引き続き適用する。

## 承認と引き渡し

承認対象はこの回答案`d1`の全文。明示的承認後に、同じ全文と実際の承認発言を含む`approved-answer.md`を最後に保存する。

回答者は回答ファイルのみを書き、Git操作を行わない。未統合の回答は未ステージ・未コミットのまま残し、質問者が検証して質問・回答案・承認済み回答をまとめて統合する。承認済み内容の訂正には、新しい関連質問と再承認が必要となる。

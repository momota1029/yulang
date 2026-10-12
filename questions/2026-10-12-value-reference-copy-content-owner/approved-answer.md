# Approved answer

Question ID: 2026-10-12-value-reference-copy-content-owner
Question revision: 2
Approved draft ID: 2026-10-12-value-reference-copy-content-owner-answer
Approved draft revision: 2
Draft history locator: questions/2026-10-12-value-reference-copy-content-owner/answer-draft.md
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revision(s): question checkpoint `6571cf780c1fbc5e7c3b444995a26e1a9d82cd01`; proof baseline `c9c2581308586dbc87542629d7389de2d2c77156`; Simple-sub reference `9bae772624c23b52a93c1b226157e16898b4d9db`
Task/thread locator: この回答会話。外部のスレッド識別子は利用不可。
Governing source/section: `notes/design/2026-10-10-parent-copy-scc-intrusion.md` の Value-reference SCC clarification、Apply-result source-fragment ownership、Definition-root Value ownership、Retained boundary；`notes/design/2026-10-08-source-generalize-definition.md` §§2–5。

## Exact approved draft content

# 回答案 — 未承認

Question ID: 2026-10-12-value-reference-copy-content-owner
Question revision: 2
Draft ID: 2026-10-12-value-reference-copy-content-owner-answer
Draft revision: 2
Predecessor/history: `answer-draft-revision-1.md`（未承認の旧案）
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revision(s): question checkpoint `6571cf780c1fbc5e7c3b444995a26e1a9d82cd01`; proof baseline `c9c2581308586dbc87542629d7389de2d2c77156`; Simple-sub reference `9bae772624c23b52a93c1b226157e16898b4d9db`
Task/thread locator: この回答会話。外部のスレッド識別子は利用不可。
Governing source/section: `notes/design/2026-10-10-parent-copy-scc-intrusion.md` の Value-reference SCC clarification、Apply-result source-fragment ownership、Definition-root Value ownership、Retained boundary；`notes/design/2026-10-08-source-generalize-definition.md` §§2–5。

## ユーザーの発言

この回答会話での発言をそのまま記録する。

> extrusionとfreshningはおなじ．コピーに相当しますね

> 参照関係はコピーしないかな．実際はSCCを計算したいので，償却のために辺を短絡するというのはありだと思うけど……

> 良さそうではあります．ただし証明で矛盾点が見つかればその限りではありません．柔軟にお願いしますね

## 解釈

「同じ」は、今回のコピー内容と Value-reference 辺の継承規則を両操作で共通にする意味と解釈する。Simple-sub における両操作の目的、型のコピー写像、極性やレベルの処理まで同一化する決定とは解釈しない。

辺の短絡への言及は、SCC 計算の効率化への許容として解釈する。具体的な短絡アルゴリズムや償却計算量はまだ選択されていない。

追加条件は、証明で具体的な矛盾が判明した際の見直しを認める意味と解釈する。証明が未完了であることや実装上の都合だけを、規則変更の根拠とはしない。

## 提案する決定と範囲

1. Extrusion と freshening の両方について、質問の選択肢②を選ぶ。型の記述・bounds をコピーしても、元の行の Value-reference 辺は継承しない。
2. コピーされた行に Value-reference 辺が生じるのは、明示的なソース所有者の構成規則がその行に参照を割り当てる場合である。コピー操作や親の記録だけでは辺を追加しない。辺をコピーしないため、この操作に伴う参照先のコピー対応も設けない。既存のソース参照と解決済み binder の同一性は維持する。
3. SCC 計算を効率化する辺の短絡は、元の参照グラフにおける SCC 判定と、そこから導く親・コピー間の intrusion 適用条件を保存することを示せる範囲で許容する。計算用の短絡を、新たなソース参照やコピーによる参照継承として扱わない。具体的な方式の採用には、その保存性と計算量の根拠が必要である。
4. この回答はコピー内容の規則を決める範囲に限る。既存の Apply・定義ルートの参照規則、Simple-sub のコピー写像、親・コピーを同じ SCC で等しくする決定を変更しない。Soundness、必要な principality、Call・effect、ソースからの構成対応の証明は未完了のままであり、実装や F5 cutover を承認するものではない。

5. この規則は、証明で具体的な矛盾または正しさを損なう反例が見つかった場合には見直す。矛盾する主張・前提・ソース構成と影響範囲を記録し、影響を受ける証明・実装だけを保留する。代替規則を検討し、独立レビューと必要なユーザー判断へ戻す。既存の承認済みの意味や対応ソース範囲を黙って変更して矛盾を回避しない。独立した作業は継続する。

## 承認

このファイル全体を回答案 revision 2 として表示し、明示的な承認を得た後にのみ `approved-answer.md` を保存する。

Pending status: 回答ファイルは未ステージ・未コミットのまま保持する。回答者は Git を変更しない。質問者が承認済みの質問・回答案・回答を検証して統合する。

## Explicit approval provenance

User approval quote: “OK”
Approval message/thread locator: この回答会話で revision 2 の全文表示と承認確認に続くユーザーメッセージ。外部のメッセージ・スレッド識別子は利用不可。
Approval date/context: 2026-10-12（会話の環境日付）。正確なメッセージ時刻は利用不可。
Revision explicitly approved: 2026-10-12-value-reference-copy-content-owner-answer, revision 2
Authorized scope: 上記回答案の全内容。Extrusion と freshening の両方で参照関係をコピーしない規則、SCC 判定と intrusion 適用条件を保存する効率化の許容、および証明で具体的な矛盾・反例が見つかった場合の見直し条件。実装・F5 cutover の承認は含まない。

Publication: 明示的承認後に完全な回答をローカル保存。未ステージ・未コミットで保持する。回答者は Git を変更しない。質問者が質問・現行回答案・回答の対応、承認、前提と範囲を検証して統合する。旧案 revision 1 は未承認の履歴であり、統合対象としての承認を含まない。確定した回答案・回答は変更せず、訂正には新しい関連質問と再承認を必要とする。

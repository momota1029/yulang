# Approved answer

Question ID: `2026-10-12-nested-extrusion-origin-value`
Question revision: 1
Approved draft ID: `2026-10-12-nested-extrusion-origin-value-answer`
Approved draft revision: 1
Draft history locator: `answer-draft.md`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): Yulang `06430602372f7c94ca8cba362fd360a728388ffa`; Simple-sub reference `9bae772624c23b52a93c1b226157e16898b4d9db`
Task/thread locator: this answering conversation; external locator unavailable
Governing source/section: `notes/design/2026-10-12-intrusion-value-type-association.md`, “Approved extrusion-event qualification” and “Qualification”; `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, “Definition-root Value ownership” and “Apply-result source-fragment ownership”

## Exact approved draft content

# 回答案 — 未承認

Question ID: `2026-10-12-nested-extrusion-origin-value`
Question revision: 1
Draft ID: `2026-10-12-nested-extrusion-origin-value-answer`
Draft revision: 1
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): Yulang `06430602372f7c94ca8cba362fd360a728388ffa`; Simple-sub reference `9bae772624c23b52a93c1b226157e16898b4d9db`
Task/thread locator: this answering conversation; external locator unavailable
Governing source/section: `notes/design/2026-10-12-intrusion-value-type-association.md`, “Approved extrusion-event qualification” and “Qualification”; `notes/design/2026-10-10-parent-copy-scc-intrusion.md`, “Definition-root Value ownership” and “Apply-result source-fragment ownership”

## ユーザーの言葉

この回答会話で、選択肢1と適用範囲について次の発言があった。

> 1だねえ．他の入れ子でも一緒．

## 解釈

選択肢1の「定義を単位にする」を選択し、同じ規則を他の入れ子にも適用する意図と解釈する。

## 提案する決定と範囲

call-demand が生む extrusion occurrence の origin Value は、その呼び出しを含む initializer/body をソース上で所有する定義の root Value とする。`if`、演算子、その他の式の入れ子でもこの規則を適用する。内側に別の定義があり、その initializer/body 内で呼び出しが生じる場合は、その内側の定義の root Value を用いる。

今回の `even` 内の `odd(n - 1)` では、origin は `E`、receiver は解決された呼び出し先 `O` とする。承認済みの Value-reference graph で `E` と `O` は同じ SCC に属するため、この occurrence の記録された型変数対に intrusion を適用し、`C = T` と `D = R` を課す。

この決定は wrapper 内にある call-demand extrusion の origin 選択を一般化する。定義 root と Apply-result Value を同一視せず、既存の Value-reference edges や親・コピー対の意味は変更しない。ソース構築・記録・輸送の実装、等置による健全性・必要な principality の保存、complete Call、effect hygiene、F5 cutover の各ゲートは、この回答だけでは閉じない。

## 承認と公開

この全文を回答案 revision 1 として表示し、明示的な承認を得た後に `approved-answer.md` を保存する。未統合の回答ファイルは unstaged/uncommitted のまま保持する。回答者は Git を変更せず、質問者が一致する質問・回答案・承認済み回答を検証して統合する。

## Explicit approval provenance

User approval quote:

> OKです

Approval message/thread locator: user message immediately following the complete displayed draft revision 1 in this answering conversation; external message/thread locator unavailable.
Approval date/context: 2026-10-12, conversation date; exact message timestamp unavailable.
Revision explicitly approved: `2026-10-12-nested-extrusion-origin-value-answer`, revision 1, for question revision 1.
Authorized scope: enclosing source-owning definition root as the origin of call-demand extrusion occurrences, including wrapper-nested calls generally; a nested definition owns calls in its own initializer/body. For the given odd/even occurrence, origin E and receiver O qualify its retained pairs for C=T and D=R under the approved Value SCC rule. Implementation, transport, preservation proofs, complete Call, effect hygiene and F5 cutover remain subject to their separate gates as stated in the exact approved draft.

Publication: finalized local answer, saved after explicit approval. The exact approved draft is preserved unchanged, including its original pending heading. Answer files remain unstaged/uncommitted; the answering primary performs no Git mutation. The questioning primary discovers, validates and integrates the matching question/draft/answer bundle. Corrections require a new linked question and renewed approval.

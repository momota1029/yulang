# Approved answer: typed Function-bound observations

Question ID: `function-bound-value-observation`
Question revision: `q1`
Approved draft ID: `function-bound-value-observation`
Approved draft revision: `r1`
Draft history locator: `answer-draft.md`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision: `13378f6bf1b9c503332127e8157a9112ff07e3a4`
Task/thread locator: unavailable; this answering conversation has no exposed locator.
Governing sources: those recorded in matching `question.md`, revision `q1`.

## Exact approved draft content

**回答案 r1**

対象質問：`function-bound-value-observation`  
質問 revision：`q1`  
回答案 revision：`r1`

**ユーザーの発言**  
「ではAで答えましょう．」

**回答としての解釈と決定範囲**  
コールバック adequacy の完全な Function bound には、選択肢Aの型付き観測への射影を採用する。具体的なデータ値の同一性や入出力間の値の相関は、比較対象の観測に含めない。

値の型、型付きインターフェースでのイベント・要求、継続、由来、および既存の `nu,K,D` の関係は保持する。値の抽象化を理由に、これらの関係や権限に関わる保証を失ってはならない。

公開型の既存基準 `zero : any -> int` を維持する。

この決定は、コールバックの証明・表示的意味論における観測境界を選ぶものとする。既存の整数の局所抽象化だけで高階コールバックまで証明済みとはしない。射影が必要な観測を保存すること、および production endpoint との対応は、引き続き証明・独立レビューの対象とする。

この回答単独では、コンパイラ実装や既存の権威ある設計文書の変更を承認しない。

## Explicit approval provenance

Decision quote: 「ではAで答えましょう．」
Publication approval quote: 「ちょっとそこは予想してなかった．勝手にそこだけコミットしてればいいと思うけど」
Approval message/thread locator: unavailable; the quotes are from consecutive user messages in this answering conversation, separated by the complete displayed r1 draft.
Approval date: 2026-10-04 (session date).
Approved revision: `r1`, the sole complete draft displayed immediately before the publication instruction. The user identified its scope contextually by 「そこだけ」 rather than spelling out the revision ID.
Authorized scope: select option A for question q1 and commit only the matching question, exact displayed r1 draft, and this approved answer. No compiler implementation or authority-record changes are authorized by this answer.

## Publication authorization

The draft was first displayed in chat while ownership was unresolved. The user's subsequent explicit instruction to commit this scope authorizes proceeding without the separate ownership-transfer confirmation requested by the assistant; it overrides that workflow prerequisite for this publication. The exact displayed draft is saved unchanged before integration. No ownership-transfer statement from the working primary is claimed. This exception records the current explicit user instruction and does not amend the general question-board workflow.

The working primary remains responsible for validating the committed handoff, writing its receipt, and recording the reviewed decision in governing sources before implementation. This publication does not automatically notify or resume the original thread.

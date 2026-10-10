# Approved answer — finalized local handoff

Question ID: `contextual-attachment-member-identity`
Question revision: `q1`
Approved draft ID: `contextual-attachment-member-identity-a1`
Approved draft revision: `a1`
Draft history locator: `questions/2026-10-10-contextual-attachment-member-identity/answer-draft.md`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision: `f352d289e5c689629d1991caa85ef7d922c82bf6` (question baseline)
Task/thread locator: this conversation; stable conversation identifier and exact message timestamp unavailable
Governing sources: `notes/design/2026-10-10-contextual-attachment-admission-design.md` §§3–6; `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–4; `rules/design-authority.md`

## Exact approved draft content

# 回答案 — 未承認

Question ID: `contextual-attachment-member-identity`
Question revision: `q1`
Draft ID: `contextual-attachment-member-identity-a1`
Draft revision: `a1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision: `f352d289e5c689629d1991caa85ef7d922c82bf6`（質問に記載された基準）
Task/thread locator: この会話。安定した会話IDと正確なメッセージ時刻は取得不可。
Governing sources: `notes/design/2026-10-10-contextual-attachment-admission-design.md` §§3–6; `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–4; `rules/design-authority.md`

## ユーザーの発言

> 意味がない話だと思います．1でいいんじゃないですかね……

## 解釈

質問q1の選択肢1を選ぶ意思として受け取る。以下はその選択を具体化した回答案であり、この版への承認は未取得。

## 決定と範囲

選択肢1を採用する。同じ具体的エフェクト注釈の出現に属するメンバーは、ひとつのattachment識別子を共有する。各メンバーのordinalと解決済みエフェクトoperandは保持する。別の注釈の出現、およびfreshなローカル実体には別の識別子を割り当てる。

これは、質問に記載されたOracleの集合単位の識別子割り当てに合わせる判断である。共有するのは注釈由来の識別子であり、異なるエフェクトの種類を同一視しない。同じエフェクト種類という理由だけで、別の由来の寄与を差し引く権限を与えない。

承認範囲は複数メンバーの注釈におけるattachment識別子の単位のみ。承認済みcarrier／two-cycle gate、注釈の極性に応じた意味を変更せず、具体的formal rowの受理やpublic/default切り替えを承認しない。

## 承認対象

回答案 `contextual-attachment-member-identity-a1`、版 `a1` の上記内容。

承認後に回答者が確定回答をローカル保存する。回答者はGit操作を行わず、質問者が質問・承認済み回答案・確定回答の組を検証してコミットする。確定後の訂正には新しい関連質問と再承認が必要。

## Explicit approval provenance

User approval quote:

> よいと思いますが，Simple-subから離れ始めているので後で注意しておきますね

Approval context: 2026-10-10, this conversation, directly following the complete display and approval request for draft `contextual-attachment-member-identity-a1`, revision `a1`. Stable conversation identifier and exact message timestamp unavailable.
Authorized scope: option 1, with exactly the decision and boundaries in the approved draft above.

## Accompanying user concern

The same approval message records the user's concern that the work is beginning to move away from Simple-sub, and their intention to revisit that concern later. Preserve this concern for the questioning primary's consideration. It is not approval of a broader departure from Simple-sub, and does not add a new design decision or alter the exact approved draft.

## Local publication

Finalized locally after explicit approval. The draft and this answer remain unstaged and uncommitted. The questioning primary discovers, validates and integrates the matching question/draft/answer bundle and records the durable decision before implementation. The answering primary performs no Git mutation. Finalized presence does not establish integration, consumption, implementation or gate completion.

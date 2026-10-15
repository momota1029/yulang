# Approved answer: initialization effect-order observation

Question ID: 2026-10-16-initialization-effect-order-observation
Question revision: 1
Approved draft ID: initialization-effect-order-observation-a1
Approved draft revision: 1
Draft history locator: answer-draft.md (complete displayed revision 1; unchanged)
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revisions: question baseline 44bc1e530; draft observed HEAD c28e89ff83f59735bf8df5b67093469bd9ee4b55
Runtime machine SHA-256: 04024174d88223e252e1d093eaee96c17d9f43d4d32bea5c41631017c9da208c
Question SHA-256: 69fb309b2db92286901cf00bbf5ef38d18d3c7bcd8540017b0bbe2ae99534e58
Approved draft SHA-256: 8b097f9d4c5b0e49790dbcb6fdabb7126c8a98eff157dee9a13eac8af6b89526
Task/thread locator: current answering conversation; stable message/thread URL unavailable
Governing sources: question.md revision 1; notes/design/2026-10-16-initialization-order-global-effects.md; approved predecessor bundle 885012b42
Status: finalized local answer; awaiting questioning-primary validation and integration

## Exact approved draft content

<!-- BEGIN EXACT APPROVED DRAFT -->
# 回答案：初期化の順序制約で数えるエフェクト

Question ID: 2026-10-16-initialization-effect-order-observation
Question revision: 1
Draft ID: initialization-effect-order-observation-a1
Draft revision: 1
Predecessor/history: none
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revisions: question baseline 44bc1e530; observed HEAD c28e89ff83f59735bf8df5b67093469bd9ee4b55
Runtime machine SHA-256: 04024174d88223e252e1d093eaee96c17d9f43d4d32bea5c41631017c9da208c
Question SHA-256: 69fb309b2db92286901cf00bbf5ef38d18d3c7bcd8540017b0bbe2ae99534e58
Task/thread locator: current answering conversation; stable message/thread URL unavailable
Governing sources: question.md revision 1; notes/design/2026-10-16-initialization-order-global-effects.md; approved predecessor bundle 885012b42
Status: draft; approval of this complete displayed revision pending

## ユーザーの発言と解釈

この回答会話で、選択肢1・2の説明に対するユーザーの回答：

> 1

これは、質問の選択肢1「各初期化の外へ出るエフェクトだけを数える」を選ぶ発言として解釈する。以下は、その選択を明文化した回答案である。

## 回答と適用範囲

1. 「エフェクトが発生した行同士は交換できない」という順序制約は、各初期化の内部ハンドラによる処理を経て、その初期化の外へ実際に出るエフェクトを対象とする。内部で処理され、外へ出ないリクエスト自体は数えない。
2. 内部ハンドラの処理や再開によって別のエフェクトが初期化の外へ出れば、それは数える。自動グローバルハンドラに届くエフェクトも、初期化の外へ出ているため数える。外へ出る初期化エフェクトをグローバルに処理するかエラーにする既存の決定は維持する。
3. 質問の例では、両初期化のリクエストがそれぞれの内部で処理されるため、内部の `ping 2 → ping 1` という順序だけでは、この順序制約への違反にならない。この判定だけでプログラム全体の受理や現在のスケジューラの正しさを認定するものではない。
4. 対象は実際に発生して外へ出るエフェクトである。宣言された許可や非空の静的エフェクト上限だけで、実際に発生したとは扱わない。

今回確定するのは順序制約の観測境界である。具体的な検出方式、スケジューリング方式、一律の依存先先行初期化、未初期化参照の処理、観測可能なエフェクトの投機実行、任意のグローバルハンドラ登録機能は承認範囲に加えない。これらの決定・証明・実装は、それぞれの既存の手順に従う。

## 確定手順

この回答案第1版の全文への明示的な承認後に、承認発言と正確な本文を含む `approved-answer.md` を保存する。回答ファイルは未ステージ・未コミットのまま残し、質問側のprimaryが検証・統合する。
<!-- END EXACT APPROVED DRAFT -->

## Explicit approval provenance

User approval quote:

> OK

Approval date/context: 2026-10-16, this answering conversation. The user replied
`OK` immediately after the complete saved revision-1 draft was displayed and the
answerer asked whether that revision could be finalized. The earlier `1` selected
the option; it is not substituted for this final approval.
Approval message/thread locator: unavailable; no stable message/thread URL supplied.
Revision explicitly approved: initialization-effect-order-observation-a1, revision 1,
for question 2026-10-16-initialization-effect-order-observation, revision 1.

Authorized scope: option 1. The relative-order rule counts effects actually
escaping each initializer after its internal handling; fully internal requests
alone do not count. Escaping effects from handler arms or resumed computation,
and effects reaching automatic global consumers, count. The exact approved draft
above supplies the complete consequences and scope boundaries. This approval
does not certify a detector, scheduler, source admission, proof closure or cutover.

## Local publication and integration boundary

The embedded draft is byte-identical to the saved and displayed revision 1;
its historical pending-approval status is preserved as part of that exact text.
This wrapper records the subsequent explicit approval without editing the draft.
This complete file is published last. All selected answer files remain unstaged
and uncommitted. The answering primary performs no Git mutation. The questioning
primary discovers and validates the matching question/draft/answer bundle,
rechecks freshness and stability, and owns integration and consumption. Local
publication does not notify another conversation or automatically resume work.
Corrections require a new linked question and renewed approval.

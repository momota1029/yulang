# 回答案 — ReadInvoke 証明の source presentation の持ち主

Question ID: `readinvoke-source-presentation-owner`
Question revision: `q1`
Draft ID: `readinvoke-source-presentation-owner-answer`
Draft revision: `a1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): 質問記載の `521f1cc0c` と、質問に挙げられた参照文書を検討。質問者が統合時に現行前提との一致を再検証する。
Task/thread locator: この回答会話。安定した外部 locator は利用不可。
Governing source/section: `notes/design/2026-10-05-source-contracts-and-common-allowance.md` §§2–3; `notes/theory/2026-10-08-readinvoke-emission-attachment-proposal.md` §§2–7; `rules/design-authority.md` Approval and implementation gate

## ユーザーの言葉と出典

> これは1のほうが良さそうですね

出典: この回答会話。安定した外部 locator は利用不可。

## 解釈

これは質問 q1 の選択肢1を選ぶ明示的な意向と解釈する。source presentation の規則と証拠を、その元規則を構成する側で一緒に作り保持する方針を選ぶ。

## 提案する決定と承認範囲

1. 質問 q1 の選択肢1を選ぶ。選択した identity `Name/Name` pure-read source-base proof では、source-construction owner が有限の source presentation を構成し、各規則の追加・lookup を示す記録をその構成と一緒に保持する。その記録を使い、元の source root における rule membership と `M_E` 導出を示す。
2. この選択は証明に使う presentation の所有場所を定める。規則の意味を新設・変更する決定ではない。元の規則スキーマ、独立に指定された意味、完全な入力 `I0/O0`、適法な作用・phase law、既存規則の存在や source-root との対応を、この回答だけで証明済みとはしない。それらは依然として必要な前提・別の証明義務であり、欠けた規則や `P.CallInitial` を presentation builder が作り出すわけではない。
3. 生成した presentation と証拠が、独立に固定された `E_c` と同一だとも、この選択だけでは主張しない。そうした既存 presentation との対応が必要な場合、その証明は別のゲートに残す。
4. 適用範囲は質問に記された有限 ReadInvoke 構成と、その元の source presentation における membership 証拠の owner seam に限る。Function / Option 2 の承認済み動作、source-rule の意味、public type-scheme 表現、F5 置換目標は変更しない。コンパイラ実装も承認しない。F5 は残る redesign ゲートと実装承認を通るまで現行実装のままとする。

この方針は、規則を作った場所で由来の記録も作るため、後から規則の所在を推測するより構成と証拠の対応を追いやすい。一方、有限な証拠構築だけで、元の規則やその意味の成立まで保証するものではない。

## 承認依頼

この保存済み回答案全文の revision `a1` を明示的に承認してほしい。承認後、同一内容と実際の承認出典を `approved-answer.md` に保存する。

Pending status: 未承認の回答案。回答者は Git 操作を行わない。承認後も回答ファイルは unstaged/uncommitted のまま残し、質問者が対応する question/draft/answer を検証して統合する。

# 確定回答 — 最初の successor Generalize の公開対象

Question ID: `successor-generalize-root-policy`
Question revision: `q1`
Approved draft ID: `successor-generalize-root-policy-answer`
Approved draft revision: `a1`
Draft history locator: `answer-draft.md`（保存・全文表示した a1）
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): 質問記載の `7eab2767f` と参照文書。質問者が統合時に現行前提との一致を再検証する。
Task/thread locator: この回答会話。安定した外部 locator は利用不可。
Governing source/section: `notes/design/2026-10-05-inferred-function-call-views.md` §§1–5; `notes/design/2026-10-05-source-contracts-and-common-allowance.md` §§2–3, 5.3; `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` Gates D–E

## 承認された回答案の正確な全文

# 回答案 — 最初の successor Generalize の公開対象

Question ID: `successor-generalize-root-policy`
Question revision: `q1`
Draft ID: `successor-generalize-root-policy-answer`
Draft revision: `a1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): 質問記載の `7eab2767f` と質問の参照文書を検討。質問者が統合時に現行前提との一致を再検証する。
Task/thread locator: この回答会話。安定した外部 locator は利用不可。
Governing source/section: `notes/design/2026-10-05-inferred-function-call-views.md` §§1–5; `notes/design/2026-10-05-source-contracts-and-common-allowance.md` §§2–3, 5.3; `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` Gates D–E

## ユーザーの言葉と出典

この会話での選択と意図：

> 2を選びたいです．つまりSimple-Subのようにshowできる程度の情報+アルファさえあれば十分であることを示したいわけですね．反論はありますか？

意図を明記する指示：

> OK．そのように意図を明白にしてください．

## 解釈

以下は回答者による具体化である。「＋アルファ」は型変数の名称ではなく、表示可能な型スキームに加えて必要となる情報を指す。Simple-Sub への言及は表現の目標を示し、既存アルゴリズムの無変更採用や、そのまま Yulang に適用できるという証明済みの主張ではない。

## 提案する決定と範囲

1. 質問 q1 の選択肢2を選ぶ。最初の具体的な source-Generalize 規則案は、保持した source Lambda root 自体ではなく、変換・抽象化した型スキームを実際の公開対象として設計する。
2. 目標は「表示可能な型スキーム＋利用時に必要な追加情報」だけで一般化・インスタンス化・利用時の型判定が成立することを示すことである。元の関数定義全体や完全な source relation の保持を、公開表現の必要条件として最初から課さない。追加情報に同じ全体を別名で保持させるだけでは、この目標を達成したことにならない。
3. 追加情報の具体的な内容と大きさは未決定とする。実際の利用側が必要とする型変数の共有、一般化可能性、外側の環境との関係、効果・権限等を調べ、各情報の必要性と抽象化の十分性を示す。規則を生成する段階で定義や内部証拠を参照することは妨げないが、利用側の型判定が元の関数定義をたどり直す必要のない公開表現を目指す。
4. 表示可能性だけから十分性を結論しない。抽象化後の実際の公開対象について、安全性、承認済みの自然な推論動作と必要な principality、一般化・インスタンス化での関係保存を証明する。既存の証明が保持 root について成立しても、それだけで変換後の公開対象の証明とはしない。必要な admission・membership と、承認済み Option 2 の production-only observations の扱いも、変換後の表現で正当化する。既存 common-allowance 案の採用や、未解決の証明義務の削除は、この選択から自動的には導かれない。
5. この決定は最初の規則案とその公開対象を選ぶ設計方針である。型推論を完成させ F5 を置き換える最終目標、再帰 SCC 等の残る対象、既存の意味契約は維持する。十分性は研究・証明すべき目標であり、達成済みとはしない。具体的な意味規則・表現・アルゴリズムの採用とコンパイラ実装は、別途の設計・独立レビュー・承認ゲートに従う。

## 承認対象

このファイル全文の回答案 `a1` を表示して明示的な承認を得た後、同じ内容と承認の出典を `approved-answer.md` に保存する。上記の選好と記載指示を、未表示だった本回答案への承認として扱わない。

Pending status: 未承認の回答案。回答者は Git 操作を行わない。承認後も回答ファイルは unstaged/uncommitted のまま残し、質問者が対応する question/draft/answer を検証して統合する。

## 明示的な承認の出典

User approval quote:

> OK．承認します．

Approval message/thread locator: この回答会話で、回答案 a1 全文の表示と「この回答案 a1 全文を承認する、でよさそうかなぁ？」への直後のユーザー返信。安定した外部 message/thread locator は利用不可。
Approval date/context: 2026-10-08（セッションの日付）、上記の全文表示に対する明示的な承認。
Revision explicitly approved: `successor-generalize-root-policy-answer/a1`（質問 `successor-generalize-root-policy/q1`）。
Authorized scope: 上記回答案「提案する決定と範囲」1–5 の全文。選択肢2を選び、表示可能な型スキームと利用時に必要な追加情報の十分性を示す設計方針を承認。十分性の証明完了や具体的な意味規則・表現・アルゴリズム・コンパイラ実装の承認ではない。

回答案の「未承認」は表示時点の状態を記録するものであり、本節の明示的な承認により a1 は承認済みとなった。回答案の原文は変更していない。

Publication: 明示的な承認後、完全な確定回答をローカルに保存。回答者は Git 操作を行わず、回答ファイルを unstaged/uncommitted のまま残す。質問者が現行前提、全文一致、承認の出典、対象範囲を検証し、対応する question/draft/answer を統合する。ローカル公開は統合・消費を意味しない。

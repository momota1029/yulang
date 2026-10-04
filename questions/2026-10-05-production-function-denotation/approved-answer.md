# Approved answer: production Function-bound denotation

Question ID: `production-function-denotation`
Question revision: `q1`
Approved draft ID: `production-function-denotation-answer`
Approved draft revision: `d1`
Draft history locator: `answer-draft.md` (complete displayed d1; preserved unchanged)
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `82e7b5a5d1e0ea0b7a3f2a8e5cdf2891201dbc32` (question source baseline)
Task/thread locator: unavailable: this conversation exposes no stable message/thread locator
Governing source/section: see the exact approved draft below.

## Exact approved draft content

# 回答案：production Function-bound denotation

Question ID: `production-function-denotation`
Question revision: `q1`
Draft ID: `production-function-denotation-answer`
Draft revision: `d1`
Status: Pending explicit approval of the complete displayed draft
Predecessor/history: 本質問の先行回答案なし。方針の前提は `../2026-10-05-production-function-bound-membership/approved-answer.md`。
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `82e7b5a5d1e0ea0b7a3f2a8e5cdf2891201dbc32`（質問の基準 revision `82e7b5a5d`）
Task/thread locator: unavailable: この会話には安定した message/thread locator が公開されていない。
Governing source/section: `notes/design/2026-10-01-coupled-effect-interface-core-draft.md` §§1–3; `notes/design/2026-10-02-source-interface-adequacy-theorem.md` §§2–4; `notes/design/2026-10-04-production-callback-endpoint-generation-draft.md` §4; `notes/design/2026-10-05-source-contracts-and-common-allowance.md` §§2.2, 3.7, 10; `notes/progress/2026-10-05-production-complete-function-interpretation-audit.md`

## ユーザーの原文と出典

2026-10-05、この回答会話でAとBの説明に続く選択発言：

> Aかな．

この発言はAの選択として記録する。以下の回答案全文への承認はまだ取得していない。

## 解釈

既存の完全な型付き観測の意味論を共通の基礎として、本番の関数型が許す振る舞いを、その型の制約を満たす観測の集合として定める方針と解釈する。この説明は回答者の解釈であり、ユーザーの原文そのものではない。

## 決定案と範囲

1. `q1`のAを選択する。本番のFunction boundのmembershipは、実際のdescriptorの元の`Rel_C`と固定された同一の`(nu,K,D)`における完全な型付き観測のうち、独立に解釈されたendpoint制約、role/entry、typed paths、発生元、継続、元のbinder scope、権限および保持された依存関係を満たすものとして定める。
2. 呼び出し側のchallenge admissionは、呼び出し位置を穴にした型付き文脈から別途定める。membershipとadmissionのいずれも、証明対象のFunction比較の成功や包含命題そのものを定義の前提にしない。
3. 前回答のOption 2を維持する。membershipを特定のソース構成子が生成する参照関係`P_ref`と同一視せず、その生成証拠を全観測の必須条件にしない。一方、四つのポートの型が合うだけで任意の発生元、継続、権限や依存関係を許すこともしない。
4. 次の証明課題は、既存の完全な関係と保持された証拠から、網羅的で比較に依存しないendpoint満足規則とadmission規則を具体化し、それを用いて本番のcallback包含を検証することである。既存の証拠ではその規則を記述できないと判明した場合、Aの選択だけでgateが閉じたとは扱わず、不足を示して必要な決定を改めて求める。
5. この回答は意味付けの基礎と次の証明方針を選択する。具体的な規則の完成、本番の適合性・健全性・principalityの証明、別の`W`/`Z`抽象化規則の採用、新しいcarrier、compiler実装は承認しない。callback Bと既存の不等式・効果証拠の契約は維持し、独立した設計レビューと必要な承認を引き続き適用する。

## 承認と引き渡し

承認対象はこの回答案`production-function-denotation-answer/d1`の全文。明示的承認後、同じ全文と実際の承認発言を含む`approved-answer.md`を最後に保存する。

回答者は選択した回答ファイルのみを書き、Git操作を行わない。未統合の回答は未ステージ・未コミットのまま残し、質問者が検証して対応する質問・回答案・承認済み回答をまとめて統合する。公開だけで別の作業の再開や回答の適用は起こらない。承認済み内容の訂正には、新しい関連質問と再承認が必要となる。

## Explicit approval provenance

User approval quote:

> OK

Approval message/thread locator: unavailable: this conversation exposes no stable message/thread locator
Approval date/context: 2026-10-05, in this answering conversation, the user's immediate reply to the complete displayed d1 and the explicit question 「この回答案 **d1の全文を承認する**、でよさそうかなぁ？」.
Revision explicitly approved: `production-function-denotation-answer/d1`, answering `production-function-denotation/q1`.
Authorized scope: Option A and the complete interpretation, constraints, and remaining proof obligations in the exact draft above. This selects the existing complete typed-observation relation as the basis of production membership, with separate comparison-independent admission. It does not approve completed concrete rules or compiler implementation.

## Publication

Finalized local publication after explicit approval. The embedded draft retains its pre-approval status and wording verbatim as approval history; this record establishes its approval. The draft and approved answer remain unstaged/uncommitted. The answering primary performs no Git mutations. The questioning primary discovers and validates the matching question/draft/answer, checks current premises and bundle stability, and owns integration and consumption. Publication neither proves the production callback theorem nor resumes another task automatically.

Finalized draft and answer content must remain unchanged. Corrections require a new linked question and renewed approval.

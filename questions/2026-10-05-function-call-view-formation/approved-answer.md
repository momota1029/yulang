# Approved answer: function-call-view-formation

Question ID: `function-call-view-formation`
Question revision: `q1`
Approved draft ID: `function-call-view-formation-answer`
Approved draft revision: `a2`
Draft history locator: `answer-draft.md`; predecessor `answer-draft-a1.md` is excluded from integration
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): question q1 records `d90ba4425038cf86ff932ed42eb309931e143fd8`
Task/thread locator: unavailable; this answering conversation has no exposed thread identifier
Governing source/section: question q1 and the governing sources identified in the exact draft below

## Exact approved draft content

# Function 呼び出し契約の形成 — 回答案 a2

Question ID/revision: `function-call-view-formation/q1`
Draft ID/revision: `function-call-view-formation-answer/a2`
Predecessor/history: `answer-draft-a1.md`; a1 への承認に推論・保護の補足が付されたため、最終公開前に改訂
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): question q1 records `d90ba4425038cf86ff932ed42eb309931e143fd8`
Task/thread locator: unavailable; this answering conversation has no exposed thread identifier
Governing sources: question q1; callback-context-delivery §§1–2; typed-computation-core-elaboration §§6, 9; source-generated-callback-structural-theorems §§2.1, 3; source-contracts-and-common-allowance §§2.2, 3, 10（いずれも question q1 に記載された `notes/design/` の文書）

## ユーザーの発言（この回答会話の原文）

> これは2でしょう．

> 承認するけど，`f`の推論は十分に一般的かつ限られている．具体的には「完全に保護されたeffectを返すhandler function」として内部で扱われるけど，handlerでないことは推論途中で（値が渡されるので）わかるという感じです．

> 後者．後`f`の返り値が保護されるのは注釈がないから．`apply(f: _ -> [io] _, x) = f x`だったら`f`からは`io`が取り除かれてもよい（ここではあんまり意味がないけど）

## 解釈と決定案

1. **選択肢2を採用する。** 関連する宣言・定義・使用、必要なら再帰成分全体から、共有された呼び出し契約を推論する。明示的な型注釈も制約生成の入力とし、注釈は必須としない。
2. **注釈なしの `f` の扱い:** `apply f x = f x` の `f` は、内部では「完全に保護された effect を返す Handler Function」として扱う。その後、`f x` で通常の値 `x` が渡されることから、推論途中で `f` が Handler ではないとわかる。根拠は `f` に具体的な Pure 関数値を渡すことではない。この内部の扱いと後続の判明を、推論規則で明示的に結び付ける。実際の関数値の役割や入口を無条件に書き換える規則には広げない。
3. **保護の根拠と注釈:** 上記の完全な保護は注釈がないことに由来する。`apply(f: _ -> [io] _, x) = f x` では、`f` からの `io` が取り除かれてもよい。これは除去を許す契約であり、この定義だけで除去が実行されるという意味には解釈しない。完全な保護は effect が空であることを意味せず、`io` の許可を他の effect 全般の除去許可へ広げない。
4. **形成元:** `F_cb` は上記のソース制約と役割・入口規則から形成し、一般化・使用時の具体化で共有を保つ。`beta` と `Slots(beta)` は元のコールバック位置と注釈の有無を含む契約から形成し、位置の同一性・スコープを保つ。型付き経路・`Flow`・owner/receiver 関係は名前解決・捕捉・引数受領・呼び出しの型付き elaboration から導く。静的な位置と実行時の受信境界は区別する。これらの具体的な生成規則は次の設計・証明義務とする。
5. **相関と独立性:** 元の `nu,K,D` 制約も同じソース成分から形成し、型・effect・位置・経路・所有関係を一つの共有割当てと元のスコープで保持する。ポートごとの独立な選択を結合しない。`Admit_F` は比較 `Q` の成否から独立させ、比較成功のために経路・受領・保護・権限を後付けしない。
6. **残る義務と範囲:** callback-literal B を維持する。期待文脈を本体の elaboration 前に届け、端点を独立に生成し、完成後に `F_lit <: F_cb` を検査する。早期伝播等には B との同値性を要求する。完成契約・profile の必要な一意性または最も一般的な解、位置・スコープの保存、admission の独立性、および第2・3項の具体的な生成・保護規則を明文化し証明する。既存 Pure 値の役割、注釈境界、Function の意味、production membership Option 2 は維持する。本回答は設計方向を選び、詳細規則・証明の完了、solver アルゴリズムや本番実装の承認を意味しない。

第2・3項の原文以外の説明と、第4〜6項の対応付けは回答者の解釈であり、承認対象に含む。

## 承認と公開

この全文 `a2` の明示的な承認後に、原文と承認の記録を含む `approved-answer.md` を保存する。a1 の承認を a2 の承認へ自動で引き継がない。a1 の履歴は保存し、今回の統合対象には含めない。

回答ファイルは未ステージ・未コミットのまま残す。回答者は Git を変更せず、質問者が一致する質問・回答案・承認済み回答を検証・統合する。最終公開後の訂正は新しい関連質問と再承認を要する。

## Explicit approval provenance

User approval quote:

> OK

Approval message/thread locator: unavailable; approval is the user message immediately following the complete display of a2 and the explicit request to approve a2 in this answering conversation.
Approval date/context: 2026-10-05, current answering conversation; a2 incorporates the user's option-2 selection and subsequent clarification of ordinary-value argument inference and annotation-dependent effect protection.
Revision explicitly approved: `function-call-view-formation-answer/a2`, answering `function-call-view-formation/q1`.
Authorized scope: the complete exact a2 above, including the answerer's explicitly identified interpretations. This selects the formation design direction and the inference/protection clarification; detailed generation rules, proofs, solver algorithm and production implementation remain gated as stated in a2.

Publication: finalized locally after explicit approval. Answer files remain unstaged/uncommitted. The answering primary performs no Git mutations. The questioning primary discovers and validates the matching question, exact current draft and approved answer, rechecks stability and integrates that bundle. The a1 archive is excluded. Finalized content must not be edited; corrections require a new linked question and renewed approval.

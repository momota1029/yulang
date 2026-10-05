# Function 呼び出し契約の形成 — 回答案

Question ID: `function-call-view-formation`
Question revision: `q1`
Draft ID: `function-call-view-formation-answer`
Draft revision: `a1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): question q1 records `d90ba4425038cf86ff932ed42eb309931e143fd8`
Task/thread locator: unavailable; this answering conversation has no exposed thread identifier
Governing source/section: question q1; `notes/design/2026-10-03-callback-context-delivery.md` §§1–2; `notes/design/2026-10-02-typed-computation-core-elaboration.md` §§6, 9; `notes/design/2026-10-04-source-generated-callback-structural-theorems.md` §§2.1, 3; `notes/design/2026-10-05-source-contracts-and-common-allowance.md` §§2.2, 3, 10

## ユーザーの発言

この回答会話で、選択肢の説明を受けたユーザーが述べた原文:

> これは2でしょう．

## 解釈

選択肢2「宣言と使用から完全なコールバック契約を推論する」を選ぶ意図と解釈する。以下はその選択を質問 q1 の各形成義務に対応させた回答案であり、この全文への承認はまだ取得していない。

## 決定案と範囲

1. **選択肢2を採用する。** 関連する宣言・定義・使用、再帰がある場合は関連する再帰成分から、共有されたコールバック契約をソース制約生成によって形成する。明示的な宣言・型注釈も入力として扱い、契約形成のために注釈を必須とはしない。
2. **`F_cb` の形成元:** 上記ソース入力と既存の役割・パラメータ入口規則から、役割を含む完全な Function インターフェースの制約を形成する。一般化・使用時の具体化を通じて共有関係を保ち、当該使用の期待インターフェースを得る。
3. **`beta` と `Slots(beta)` の形成元:** 元のソース上のコールバック位置とその契約形成から、静的な位置の同一性と profile の位置一覧を形成する。推論・一般化・具体化・輸送を通じて元の同一性とスコープを保存する。静的な位置と、実行時に有効化される受信境界は区別する。
4. **型付き経路・`Flow`・owner/receiver 関係の形成元:** ソースの名前解決、捕捉、引数受領、呼び出し、および既存の型付き elaboration 規則から導く。型の形や比較成功だけを根拠に、経路・受領・権限を作らない。
5. **元の `nu,K,D` 制約の形成元:** 同じ関連ソース成分の制約生成から、型・effect・位置・経路・所有関係の相関を一つの元の共有割当てとスコープのもとに保持する。各ポートを独立に選んで結合しない。`Admit_F` の根拠は比較 `Q` の成否から独立させ、`Q` を成功させるための条件の後付けを認めない。
6. **既決事項と残る義務:** callback-literal B を保存し、期待文脈を本体の elaboration 前に届け、端点は独立に生成し、完成後に `F_lit <: F_cb` を検査する。早期伝播や循環する依存の処理には B との同値性を要求する。完成契約・profile が必要な範囲で一意または最も一般的に定まること、ソース同一性・スコープの保存、比較から独立した admission を証明する。既存 Pure 値の役割、注釈境界、Function の意味、承認済み production membership Option 2 は維持する。この回答は形成規則の設計方向を選び、詳細な推論規則・証明・solver アルゴリズム・本番実装の完了や承認を意味しない。

## 承認

この全文を回答案 `a1` として表示し、明示的な承認を得てから `approved-answer.md` を保存する。

Pending status: answer files remain unstaged/uncommitted, including after approval. The answering primary performs no Git mutations. The questioning primary validates and integrates the matching approved bundle. Corrections to finalized answers require a new linked question and renewed approval.

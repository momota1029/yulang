# 監査用 dot への現在の指示 (監督役が書く)

更新: 2026-11-08（監督役）。dot は編集しない。
- 指示の ID: A-1
- 状態: ACTIVE（`STOP` と書き換えたら、次のサイクルで止まる）
- 最大サイクル数: 12

## 現在の指示

計画表 `notes/plan/m1-plan.md` の **T15（Yulang2 の再現監査）** と **F1**。常設の指示は `notes/plan/dots-audit-standing-orders.md`。

優先順位（上から。1 サイクルでは終わらない）:
0. **適合例 X1〜X25 を Yulang2 の実機に通す（最初に、最優先）**: `notes/handoff/2026-11-08-m1-spec-examples-conformance.md` の各例を、Yulang の最小のコードにして実機で実行し、結果（型、診断、実行結果）を `notes/audit/x-oracle.md` に表にする（列: X の ID／入力のコード／Yulang2 の結果／spec の期待／一致・違う・実機で表せない／備考）。実機で表せない例（宣言の拒否が診断として出ない、など）は、その理由を書く。違い・食い違いは、質問ノートか spec の追記案へ。これが、証明用の dot が「Yulang2 と合っているか」を確かめながら進める基準になる。
1. **F1 の確認（最初に）**: ユーザーの説明（`spec/05-effects.md` 5.5c）「`'a -> ['e] 'b` は `'a ['f] -> ['e, 'f] 'b` に cast できる。引数の行は空でなく全能。効果は関数の起動時に放出される」を、Yulang2 の実装（`crates/infer` の部分型・application・cast まわり）と、実機の例で確かめる。実機の例は、効果のある引数を普通の関数に渡す形、高階の引数に普通の関数を渡す形、`x | f`。**新しい spec と Lean の核（`lean/Yulang/Common.lean` の `common_arrow_iff`、application の型付け）に入っているか**を、根拠つきで報告する。
2. **効果と型の文書**: `main:web/docs/ja/reference/effects.md`、`types.md`、`type-theory.md`、`functions.md`、`application.md`、`main:spec/2026-05-31-effect-variable-subtractable.md`、`main:notes/design/handler-row-subtraction.md` の主張を抽出し、実機に通し、新 spec と Lean に突き合わせる（`notes/audit/y2-claims-effects-types.md`）。
3. **cast と role**: `casts.md`、`main:spec/2026-06-02-role-system.md`、`2026-06-06-invariant-type-sandwich.md`、`2026-06-04-method-selection.md`（`notes/audit/y2-claims-casts-roles.md`）。
4. **制御構文・パターン・record・構文**: `control-flow.md`、`patterns.md`、`structs.md`、`operators.md`、`idioms.md`、`syntax-style.md`、`errors.md`、`main:spec/2026-06-06-syntax-design.md`、`2026-06-25-act-copy.md`（`notes/audit/y2-claims-control-patterns.md`）。
5. 後回し: モジュール、標準ライブラリ、資源 API（file/server/instant）、runtime/mono/VM の文書（型推論の核とは別の層）。

## 完全性の側の例も集める（ユーザーとの話から, 2026-11-08）

正しさは、健全性（誤った型を付けない）、完全性（宣言した範囲の正しいプログラムを拒否しない）、主型性の三つ組。適合例は拒否の例に偏っているので、監査では**Yulang2 が受理して意味のあるプログラム**を、「通るべき例」の候補として積極的に拾う（`notes/audit/x-oracle.md` に、列「通る／拒否」を足す）。拒否の例には、**なぜ拒否されるか**（仕様の決定として、どの節の規則か）を必ず書く。仕様にない理由で拒否されている例（実装の都合のように見えるもの）は、質問ノートにする。

## 参照

`spec/00-sources.md`（素材の所在）、`spec/` 全体（新 spec）、`lean/README.md`（Lean の定理の一覧）、`notes/handoff/2026-11-08-m1-model-fidelity-audit.md`（作業 0 の監査。先行する監査の形式）、`notes/reference/`（旧世代の区間規則の写し）、`notes/handoff/2026-11-08-m1-spec-examples-conformance.md`（適合例 X1〜X25）。

## 監督役からのコメント

（サイクル報告を読んだあとに書く。）

## 停止（ユーザー決定 2026-11-09）

監査 dot（`work/dots-audit`）は、サイクル 5 で区切りとする。X1–X25 の Yulang2 実機照合と F1 の有限観測は一巡し、新 spec・Lean の意味論に影響する発見は出尽くした。動的 demand provenance の調査は、旧実装の切り分けにとどまるため行わない。次の監査サイクルが起動しても、**作業を始めず**、心拍に `status: stopped` と書いて終了すること。再開は、ユーザーの指示（新しい監査対象が出たとき）による。

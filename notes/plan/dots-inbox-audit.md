# 監査用 dot への現在の指示 (監督役が書く)

更新: 2026-11-08（監督役）。dot は編集しない。
- 指示の ID: A-1
- 状態: ACTIVE（`STOP` と書き換えたら、次のサイクルで止まる）
- 最大サイクル数: 12

## 現在の指示

計画表 `notes/plan/m1-plan.md` の **T15（Yulang2 の再現監査）** と **F1**。常設の指示は `notes/plan/dots-audit-standing-orders.md`。

優先順位（上から。1 サイクルでは終わらない）:
1. **F1 の確認（最初に）**: ユーザーの説明（`spec/05-effects.md` 5.5c）「`'a -> ['e] 'b` は `'a ['f] -> ['e, 'f] 'b` に cast できる。引数の行は空でなく全能。効果は関数の起動時に放出される」を、Yulang2 の実装（`crates/infer` の部分型・application・cast まわり）と、実機の例で確かめる。実機の例は、効果のある引数を普通の関数に渡す形、高階の引数に普通の関数を渡す形、`x | f`。**新しい spec と Lean の核（`lean/Yulang/Common.lean` の `common_arrow_iff`、application の型付け）に入っているか**を、根拠つきで報告する。
2. **効果と型の文書**: `main:web/docs/ja/reference/effects.md`、`types.md`、`type-theory.md`、`functions.md`、`application.md`、`main:spec/2026-05-31-effect-variable-subtractable.md`、`main:notes/design/handler-row-subtraction.md` の主張を抽出し、実機に通し、新 spec と Lean に突き合わせる（`notes/audit/y2-claims-effects-types.md`）。
3. **cast と role**: `casts.md`、`main:spec/2026-06-02-role-system.md`、`2026-06-06-invariant-type-sandwich.md`、`2026-06-04-method-selection.md`（`notes/audit/y2-claims-casts-roles.md`）。
4. **制御構文・パターン・record・構文**: `control-flow.md`、`patterns.md`、`structs.md`、`operators.md`、`idioms.md`、`syntax-style.md`、`errors.md`、`main:spec/2026-06-06-syntax-design.md`、`2026-06-25-act-copy.md`（`notes/audit/y2-claims-control-patterns.md`）。
5. 後回し: モジュール、標準ライブラリ、資源 API（file/server/instant）、runtime/mono/VM の文書（型推論の核とは別の層）。

## 参照

`spec/00-sources.md`（素材の所在）、`spec/` 全体（新 spec）、`lean/README.md`（Lean の定理の一覧）、`notes/handoff/2026-11-08-m1-model-fidelity-audit.md`（作業 0 の監査。先行する監査の形式）、`notes/reference/`（旧世代の区間規則の写し）、`notes/handoff/2026-11-08-m1-spec-examples-conformance.md`（適合例 X1〜X25）。

## 監督役からのコメント

（サイクル報告を読んだあとに書く。）

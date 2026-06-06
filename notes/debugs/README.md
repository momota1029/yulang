# notes/debugs — yulang-infer 残り failing test の診断＋fix spec

2026-06-06 時点。`cargo test -p yulang-infer -- --skip compiled` が **490 passed / 7 failed**。
この 7 件（テストは 6 グループ）を Codex に渡して直すための、1 件 1 ファイルの診断書。
各ファイルに「入力 / 期待値 / 実際値 / なぜ期待値が正しいか（手計算）/ 診断 / 見るべき場所 / 修正方針」を書いた。

経緯（memory）: `invariant-type-sandwich` / `infer-test-pass-2026-06-06` / `project_infer_residual_regression`。

## Codex への規約（厳守）

1. **テスト期待値を書き換えるな**。各 doc の「期待値」は手計算で確定済み・正しい。
   fix の結果テストが別の値を要求してきたら、**期待値を直さず STOP して報告**すること。
   （残差表記を握り潰して期待値を改竄する前科があるので、ここは特に厳守。）
2. **テストファイルは触らない**: `crates/yulang-infer/src/tests.rs`,
   `crates/yulang-infer/src/source/tests.rs`, `crates/yulang-infer/src/display/dump.rs`。
   直すのは実装だけ。レビューで test の diff があれば `git checkout` で却下する。
3. **1 bug = 1 commit**。回帰したら revert。
4. 完了判定: `cargo test -p yulang-infer -- --skip compiled` で対象が緑になり、
   **他の 490 件を 1 件も壊さない**こと。

## 一覧（推奨順）

| # | ファイル | テスト | 委譲 | risk |
|---|---|---|---|---|
| ✅⑦ | [branch-join-cast](branch-join-cast.md) | `branch_join_uses_implicit_cast_boundary` | — | **済 `1388c03`**（(B') で実装・検証済）|
| ✅⑥ | [string-role-toplevel](string-role-toplevel.md) | `lowers_string_role_impls_from_implicit_prelude` | — | **済 `c026491`**（apply で deferred selection 先行解決）|
| ④⑤ | [std-var-ref-effect-annotation](std-var-ref-effect-annotation.md) | `lowers_std_var_ref_*` ×2 | 保留 | **設計未確定**（反変 effect 推論・①と同根・期待値が変わる）|
| ⑫ | [handler-continuation-any-leak](handler-continuation-any-leak.md) | `handler_continuation_..._avoids_top_in_effect_row` | ○ | 要調査 |
| ① | [ref-update-cooccur-overmerge](ref-update-cooccur-overmerge.md) | `render_compact_results_handles_ref_update_effect` | △ | **高（cooccur 本丸 2420 行・前科あり）** |
| ⑧ | [choice-residual-overremoved](choice-residual-overremoved.md) | `choice_effect_residual_coalesces_across_open_rows` | ✗ | 不明（仮説なし・①の後）|

## perf / 状態不明（バグ表とは別カテゴリ）

- [compiled-tests-slow](compiled-tests-slow.md) — `compiled` テスト ~30 件が極端に遅く、
  普段 `--skip compiled` で飛ばしているため**現在 pass しているか不明**。高速化＋現状把握を依頼。

## レビュー側（Claude）の運用

- test ファイルは無条件で `git checkout` して手で再判定 → 実装だけ温存。混在ファイル注意。
- ④⑤ は反変 effect 推論の設計が未確定（**期待値そのものが変わる見込み**）。①と同根なので、
  ①を先に直してから取り組む。確定までは Codex に渡さない。
- ① は単独 commit、全 490 件の回帰を最優先で確認してからレビュー。

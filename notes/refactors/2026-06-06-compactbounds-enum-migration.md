# 引き継ぎ: `CompactBounds` を struct → enum に移行（機械的リファクタ）

担当想定: Codex（機械的・compiler 主導）。設計とロジック（sandwich・display）は別途、人間/Claude 側が持つ。
背景設計: `spec/2026-06-06-invariant-type-sandwich.md` を必ず読むこと。

## ゴール

`crates/yulang-infer/src/simplify/compact.rs` の `CompactBounds` を struct から enum に変える。
今は `Interval` 変種ただ1つ（lift 変種 Con/Tuple/Fun… は**この作業では作らない**。後で sandwich 実装時に追加）。
**完全に振る舞い保存**のリファクタ。型の出力・推論結果は一切変えない。

```rust
// 移行後の最終形（compact.rs）
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum CompactBounds {
    Interval {
        self_var: Option<TypeVar>,
        lower: CompactType,
        upper: CompactType,
    },
}

impl Default for CompactBounds {
    fn default() -> Self {
        CompactBounds::Interval { self_var: None, lower: CompactType::default(), upper: CompactType::default() }
    }
}
```

メソッドは**既に struct に実装済み**（`interval()`, `lower()`, `upper()`, `lower_mut()`,
`upper_mut()`, `self_var()`, `self_var_mut()`）。enum 化したら本体を `match self { Interval{..} => .. }`
へ書き換えるだけ（下記参照）。

## スコープ（実測）

- `.lower` / `.upper` 読み: ~631、`.self_var` 読み: ~57
- 書き込み/`&mut`: `.lower`/`.upper` ~47、`.self_var` も少数
- `CompactBounds { .. }` 構築・分解パターン: ~127
- 約35ファイル（`grep -rEl '\.(lower|upper)\b' src/` で一覧）

## 進め方（2フェーズで緑を保つ）

### フェーズ1: 読みをアクセサへ寄せる（struct のまま・緑維持）

フィールドとメソッドは別名前空間なので、struct のままでも `x.lower`（フィールド）と
`x.lower()`（メソッド）は両立する。まず**読みだけ**をメソッドへ移す。各フェーズ後 `cargo build` 緑を確認。

- `x.lower`（読み）→ `x.lower()` ／ `x.upper` → `x.upper()` ／ `x.self_var` → `x.self_var()`
- `&x.lower` → `x.lower()`（`lower()` が `&CompactType` を返すので `&` は落とす。`&&` になったら直す）
- `x.lower.clone()` → `x.lower().clone()`、`x.lower.vars`（読み）→ `x.lower().vars` など
- **書き込み・mut は触らない**（`x.lower = ..`, `&mut x.lower`, `x.lower.vars.insert(..)` 等はフェーズ1では放置）
- **構築・分解 `CompactBounds { .. }` も触らない**

### フェーズ2: struct → enum＋書き込み/構築を直す

1. `compact.rs` の `struct CompactBounds { .. }` を上記 enum へ。`impl Default` 追加。
   `#[derive(.., Default, ..)]` から `Default` を外す（手書き impl にする）。
2. 7メソッドの本体を `match self { CompactBounds::Interval { lower, .. } => lower }` 等へ。
   `interval()` は `CompactBounds::Interval { self_var, lower, upper }` を返す。
3. compiler エラー（E0609「no field lower on CompactBounds」/ E0560 など）を潰す:
   - 構築 `CompactBounds { self_var, lower, upper }` → `CompactBounds::Interval { self_var, lower, upper }`
     （または `CompactBounds::interval(self_var, lower, upper)`）
   - 分解パターン `CompactBounds { lower, upper, .. }` → `CompactBounds::Interval { lower, upper, .. }`
   - 書き込み `x.lower = v` → `*x.lower_mut() = v`、`x.self_var = v` → `*x.self_var_mut() = v`
   - `&mut x.lower` → `x.lower_mut()`、`x.lower.vars.insert(..)`（mut）→ `x.lower_mut().vars.insert(..)`
   - フェーズ1で漏れた読みも E0609 で出るので `x.lower()` へ

## 触ってはいけないもの（compiler が自然に弾くが念のため）

`.lower` / `.upper` は他の型にもある。これらは **CompactBounds ではない**ので変えない:
- `Infer.lower` / `Infer.upper`（`RefCell<FxHashMap<..>>`、`solve/mod.rs:377-378`）。
  `infer.lower.borrow()`, `self.lower.borrow()` 等はそのまま。
- `tests.rs` のテスト用 struct（`expected_callee.lower.is_some()`, `evidence.expected.lower` 等、`Option`）。

enum 化後、compiler エラーが出るのは **CompactBounds のフィールドアクセスだけ**なので、
「`cargo build` のエラー箇所を潰す」だけで型安全に判別できる。エラーの出ない `.lower`/`.upper` は触らない。

## 絶対にやってはいけないこと

- **テストの期待値を一切変えない。** これは振る舞い保存リファクタ。下記16テストは元から赤で、
  それ以外が赤くなったら**それは移行のバグ**。実装を直すこと。テスト側 `.yu` 文字列や `assert_eq!`
  の右辺を書き換えて辻褄を合わせるのは厳禁（混在ファイルでも test 部分は不可）。
- **sandwich / lift 変種（Con/Tuple/Fun…）を実装しない。** Interval ただ1変種のままにする。
- `finalize_expansive_compact_scheme`（compact.rs の crutch）のロジックは変えない（アクセサ移行のみ）。
- serde 形式が enum タグ付きに変わるのは想定内（キャッシュは再生成される）。`--skip compiled` で回避。

## 検証（パリティ・ゲート）

```fish
cd /home/momota1029/rust/yulang/crates/yulang-infer
env RUSTC_WRAPPER= cargo build -p yulang-infer            # 緑
env RUSTC_WRAPPER= cargo test -p yulang-infer --lib --no-fail-fast -- --skip compiled
```

最終結果が **`481 passed; 16 failed`** で、赤が**ちょうど次の16個**であること（増減ゼロ）:

```
display::dump::tests::render_compact_results_handles_ref_update_effect
source::tests::compact_scheme_keeps_invariant_payload_interval
source::tests::lowers_nested_list_pattern_wildcards_from_source_loader
source::tests::lowers_opt_if_join_keeps_invariant_payload_interval
source::tests::lowers_opt_if_join_without_annotation_keeps_open_payload_interval
source::tests::lowers_record_pattern_spread_source
source::tests::lowers_std_list_helpers_through_implicit_prelude
source::tests::lowers_std_var_ref_inside_nested_act_module
source::tests::lowers_std_var_ref_through_top_level_alias
source::tests::lowers_string_role_impls_from_implicit_prelude
tests::branch_join_uses_implicit_cast_boundary
tests::choice_preserves_parse_residual_on_callback_and_result_effects
tests::function_effect_annotation_clears_subtractability_on_parameter_occurrence
tests::handler_continuation_in_queue_principal_avoids_top_in_effect_row
tests::non_through_lower_clears_through_on_var_propagation
tests::row_effect_annotation_clears_subtractability_when_argument_reaches_output
```

注意:
- `RUSTC_WRAPPER=`（空）を必ず付ける（sccache のタイムアウト回避）。
- `--skip compiled`（compiled_* は遅くて full suite がタイムアウトする）。
- fish なら status は `$status`、リダイレクトは `&>`。

## 完了後

このファイルに「完了・最終 test 結果・気づき」を追記して残すこと。
次工程（sandwich 実装 = `spec/2026-06-06-invariant-type-sandwich.md` の Step 3 以降）は別担当。

## 完了ログ

2026-06-06:

- `CompactBounds` を `Interval { self_var, lower, upper }` だけを持つ enum に移行した。
- 既存の field read/write/構築/分解を accessor・mut accessor・`CompactBounds::Interval` へ機械的に移した。
- sandwich / lift 変種は追加していない。`finalize_expansive_compact_scheme` のロジックも enum 化に必要な accessor 置換のみ。
- `env RUSTC_WRAPPER= cargo build -p yulang-infer` は成功。`scc/close.rs` の unused helper warning が 2 件出る。
- `env RUSTC_WRAPPER= cargo test -p yulang-infer --lib --no-fail-fast -- --skip compiled` は想定どおり
  `481 passed; 16 failed; 0 ignored; 0 measured; 30 filtered out`。
- 失敗 16 件は上の「検証」節のリストと一致。増減なし。
- 気づき: `cargo build` では test module 内の `CompactBounds` field access が出ないため、`cargo test --lib --no-run`
  相当の test target compile まで見る必要があった。

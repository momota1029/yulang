# compiled テスト群が極端に遅い（＋ skip 中で pass 状態が不明）

## 症状
`cargo test -p yulang-infer` で、テスト名に `compiled` を含む ~30 件
（`527 = 492 + 5 + 30` の 30）が**極端に遅い**（手動 abort するレベル）。
日常の確認は `-- --skip compiled` で飛ばしているが、その結果
**これらが今 pass しているか不明**（skip を外すとエラーが出る可能性）。

## 何をするテスト群か
std ライブラリの「コンパイル単位 artifact / bundle / namespace artifact」系
（`crates/yulang-infer/src/source/tests.rs`）。例:
`compiled_typed_artifact_preserves_schemes_and_validates_symbols`,
`compiled_namespace_artifact_preserves_operator_value_identity` 等。
`build_compiled_unit_artifacts` / `build_compiled_typed_artifacts` /
`build_compiled_namespace_artifacts` を呼び、lib/std 全体を lower してから artifact を作る。

## 遅さの機序（計測で絞り込み済み）
- 30 本中、>60s かかるのは **3 本だけ**:
  `compiled_std_runtime_bundle_carries_non_unit_runtime_dependencies`,
  `compiled_typed_import_preserves_associated_role_method_output_for_root_expr`,
  `compiled_typed_import_preserves_unqualified_prelude_variant_pattern_shape`。
  残り 27 本は速い。総計 96s ≒ **std typed/semantic bundle の 1 回ビルド(~90s)** が支配項。
- うち `..._unqualified_prelude_variant_pattern_shape`(source/tests.rs:1014) は
  `cached_std_compiled_unit_*`(OnceLock, 26-75) を使う＝**既にキャッシュ済み**。
  なのに >60s ＝「dup ビルド」より **std 全体の typed 推論ビルドそのものが ~90s 遅い**のが本体
  （OnceLock の 1 回ビルドに 3 本が同時に張り付いている形）。
- つまり主因は重複作業ではなく **std lib 全体の型推論が単純に重い**。`build_compiled_*` 直呼び
  （387, 1849…）の dup は副次的（namespace 系は速い）。

## 速くする方向（候補）
- (A) **std bundle をディスク永続キャッシュから読む**: `artifact_cache`
  （`writes_and_reads_compiled_unit_artifact` が既にある）で std typed/semantic bundle を 1 度だけ
  作って保存→テストは読込のみにし、in-process の再ビルドを消す。
- (B) **std 推論自体を速くする**: ~90s の内訳を profile。finalize / cooccur に時間が偏っていれば
  ①（cooccur 過剰作業）と同根の可能性。①を直すと自然に速くなるかも（要確認）。

## Codex への依頼
1. **profile**: 現状は 30/30 pass・96s（隠れエラー無し、下記計測参照）。遅さの本体は
   std typed bundle の 1 回ビルド ~90s。まずこの ~90s の内訳を計測（lower / finalize /
   cooccur / artifact 化 のどこに時間が偏るか）。落ちるテストが出たら別途バグとして報告
   （**期待値は勝手に変えない**）。
2. **遅さの所在を特定**: どのテストが std を再 lower しているか、`build_compiled_*` 直呼びを
   キャッシュ（`OnceLock` / 共有 lowered std state）経由に寄せられないか。
3. **高速化**: std lowering 結果を 1 度だけ作って共有する。artifact 種別ごとに cache helper を
   足すのが素直（既存 2 helper と同じ形）。**意味は変えない**（同じ artifact が出ること）。

## 厳守
- テストファイルの**期待値・assert を緩めない**。遅さは「速くする」、エラーは「直す or 報告」。
- 高速化でテストの検査内容を削らない（artifact の同一性チェックは残す）。
- 無回帰: `cargo test -p yulang-infer`（skip 無し）で全件緑を目標。**所要時間も併記して報告**。

## 現状（Claude 計測 2026-06-06）
- `cargo test -p yulang-infer compiled`: **30 passed / 0 failed**、**finished in 96.32s**。
  → **隠れエラーは無い**（skip を外しても全部素直に pass）。問題は遅さのみ。
- 遅いのは上記 3 本（各 >60s）。＝ std typed bundle の 1 回ビルドが ~90s。残り 27 本は速い。

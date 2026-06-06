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

## 遅さの機序（仮説）
- std 全体の lowering（`lower_source_set` with `std_root`）が高コスト（infer をフルで回す）。
- `cached_std_compiled_unit_artifact_bundle()` /
  `cached_std_compiled_unit_semantic_artifact_bundle()` は `OnceLock` で std bundle を
  キャッシュしている（source/tests.rs:26-75）が、
- **キャッシュを使わず `build_compiled_*` を直接呼ぶテストが複数ある**
  （source/tests.rs:387, 1849, 1904, 1972, 2057 …）。これらは毎回 std を丸ごと lower し直す
  ＝ N 本 × フル std 推論。ここが効いていると思われる。

## Codex への依頼
1. **まず現状把握**: `cargo test -p yulang-infer compiled`（skip 無し）を一度通して、
   (a) 実時間 (b) pass/fail を記録。落ちるものがあれば、それは別途バグとして切り出す
   （**テスト期待値は勝手に変えない**。落ちる理由を報告）。
2. **遅さの所在を特定**: どのテストが std を再 lower しているか、`build_compiled_*` 直呼びを
   キャッシュ（`OnceLock` / 共有 lowered std state）経由に寄せられないか。
3. **高速化**: std lowering 結果を 1 度だけ作って共有する。artifact 種別ごとに cache helper を
   足すのが素直（既存 2 helper と同じ形）。**意味は変えない**（同じ artifact が出ること）。

## 厳守
- テストファイルの**期待値・assert を緩めない**。遅さは「速くする」、エラーは「直す or 報告」。
- 高速化でテストの検査内容を削らない（artifact の同一性チェックは残す）。
- 無回帰: `cargo test -p yulang-infer`（skip 無し）で全件緑を目標。**所要時間も併記して報告**。

## 現状（Claude 計測）
- 計測中（バックグラウンドで `cargo test -p yulang-infer compiled` 実行 → 結果が出たら追記）。

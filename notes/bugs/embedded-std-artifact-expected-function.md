# embedded std artifact 経路で `expected function` × 4

## 解消（2026-05-20）

原因は compiled runtime surface merge の runtime ID remap 漏れだった。
`Stmt::Let` の `value` は走査していたが `pattern` は走査しておらず、
record pattern default expression 内の `ApplyEvidence` が古い expected-edge ID を
指したまま残っていた。その結果、artifact 合成後に `callee_source_edge` が
`ApplicationArgument` edge を指し、runtime lowerer の validation に落ちていた。

`Pattern` 全体を remap 対象にし、record pattern field default expression も
`remap_core_expr_runtime_ids` に通すようにした。`crates/yulang-wasm` の
`compile_and_run` は compiled std runtime surface を default ON に戻し、
無効化したい場合だけ `YULANG_WASM_DISABLE_COMPILED_STD_SURFACE` を使う。

この修正後も同一 source の 2 回目だけ `expected function` fallback が出た。
こちらは compiled typed surface に保存された build-time `TypeVar` と runtime
lowering の fresh `TypeVar` allocator が同じ番号を再利用する別問題だった。
import 時に artifact 内の最大 `TypeVar` まで allocator を予約し、artifact 由来の
scheme と user lowering の型変数 ID が衝突しないようにした。

回帰確認:

```bash
cargo test -q -p yulang-infer compiled_runtime_bundle_remaps_record_pattern_default_apply_evidence
cargo test -q -p yulang-wasm compiled_std_bundle_reuses_same_source_without_fallback
cargo test -q -p yulang-wasm compiled_std_bundle_matches_oracle_on_playground_tour -- --include-ignored
```

## 過去の状況

`crates/yulang-wasm` は build.rs で std を pre-lower した `Vec<CompiledUnitArtifact>` を
postcard で焼き込んでいる。これを実行時に
`lower_source_set_with_compiled_unit_artifacts_profiled` 経由で再利用すれば、
毎回 std を素から lowering する必要がなくなる（playground 体感ロード短縮の本命）。

実装上の入口は `crates/yulang-wasm/src/lib.rs` の `compile_and_run`。
そこに `YULANG_WASM_USE_COMPILED_STD_SURFACE` env var ゲートが入っており、
wasm32 では env var が常に空なので「**embedded 経路は default OFF**」になっている。
これは `commit 69e51ba Use std oracle cache for wasm runs` で追加されたガード。

## 再現

`compile_and_run` を以下に差し替えて wasm を再ビルド:

```rust
fn compile_and_run(source: &str) -> Result<CompileRunOutput, String> {
    compile_and_run_with_embedded_std(source, true, None)
}
```

playground を起動して Tour example を Run すると、コンソールの
`Yulang run timings` に以下が出る:

```json
{
  "compiled_std_cache_hit": false,
  "compiled_std_fallback_reason":
    "embedded std artifact diagnostics: expected function\nexpected function\nexpected function\nexpected function"
}
```

embedded 経路で 4 件の `expected function` surface diagnostics が出て、
`compile_and_run_with_embedded_std` の網羅的フォールバックが発火し source cache 経路へ。
結果 cache hit ゼロのまま source から std を lowering し直すので、
embedded 試行ぶんだけ余計に時間がかかり、体感はむしろ悪くなる。

## いまの判断（2026-05-17）

monomorphize リファクタ（`notes/bugs/type-monorphized-refactor.md`）の途上で
typed IR の表面が動いている最中なので、ここを今手当てしても無駄になる可能性が高い。
リファクタが落ち着いたら再度有効化して `expected function` が消えているか確認する。

短期では env var ゲートのまま放置（=default OFF）としていた。
postcard 化や artifacts キャッシュ（`with_embedded_std_compiled_unit_artifacts`）は
有効化時の土台として残してある。

## 再有効化時のチェック手順

1. `compile_and_run` の env var ゲートを外して default ON にする
2. `npm run build:wasm && npm run dev` で playground 起動
3. Tour example を Run、コンソールで `compiled_std_cache_hit: true` かつ
   `compiled_std_fallback_reason` が無いことを確認
4. 他の example（特に non-determinism / handler / junction）も同様に確認
5. 問題なければ env var ゲート自体を削除して整理

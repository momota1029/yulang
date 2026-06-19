# bytes / path 型の実装 引き継ぎ

最終更新: 2026-05-16 (りな / Codex)

## ゴール

`std::fs` を `notes/design/std-fs.md` の方針に揃えるために、その前提となる `bytes` と `path` の二つの型を処理系に追加する。

### 設計合意（このセッションで決まったもの）

1. **`bytes`**: 永続バランス木で表す（`crates/yulang-runtime/src/runtime/bytes_tree.rs` = `StringTree` のバイト版）
2. **`path`**: 内部表現は `Rc<std::path::PathBuf>`（Rust の `PathBuf` を借りる）。WTF-8 周りの非 UTF-8 対応も Rust 任せ
3. **変換の非対称**:
   - `path → bytes`: 暗黙変換。`cast(p: path): bytes = …` を std で宣言する
   - `bytes → path`: 明示関数のみ（`path::of_bytes`）
   - `bytes → str`: 明示関数のみ。host 境界では `(str, int)` タプル（lossy 文字列 + valid byte count）で返し、Yulang 側で raw / `[warn]` / `[throw]` のラッパーを用意
4. **bytes の Display/Debug は実装しない**。`b.to_hex` / `b.to_utf8_lossy` 等の明示変換 method 経由で人間向けに見せる
5. **`path` の literal 構文は作らない**

詳しい背景: `notes/design/std-fs.md`, `examples/12_cast.yu`（cast 宣言の例）

## 完了済み

### (1) `BytesTree` 実装
- 追加: `crates/yulang-runtime/src/runtime/bytes_tree.rs`（`StringTree` のバイト版、byte 単位の len/index/concat/splice）
- `crates/yulang-runtime/src/runtime/mod.rs` に `pub mod bytes_tree;` を追加
- テスト 4 件が `cargo test -p yulang-runtime bytes_tree` で通る

### (2) `bytes` 型の wiring

**新規 PrimitiveOp**: `StringToBytes`, `BytesLen`, `BytesEq`, `BytesConcat`, `BytesIndex`, `BytesIndexRange`
- `crates/yulang-typed-ir/src/expr.rs` — `PrimitiveOp` enum に 6 variant 追加
- `crates/yulang-typed-ir/src/graph.rs` — `PrimitiveTypeFamily::Bytes` 追加

**Infer 側**:
- `crates/yulang-infer/src/lower/builtin_types.rs` — `PrimitiveTypeFamily::Bytes`、source alias `"bytes"`、std path `("bytes", "bytes")` 登録
- `crates/yulang-infer/src/lower/primitives/scalar.rs` — `install_bytes_*` ヘルパ 6 個追加
- `crates/yulang-infer/src/lower/primitives/mod.rs` — `bytes_module` 用意、`install_*` 呼び出しを足した

**Runtime VM 側**:
- `crates/yulang-runtime/src/vm/model.rs` — `VmValue::Bytes(BytesTree)` 追加
- `crates/yulang-runtime/src/vm/mod.rs` — `use crate::runtime::bytes_tree::BytesTree;` と `ExpectedBytes(VmValue)` エラー variant
- `crates/yulang-runtime/src/vm/value.rs` — `bytes_value()` ヘルパ追加
- `crates/yulang-runtime/src/vm/primitive.rs` — arity マッチ と apply ハンドラ 6 個
- `crates/yulang-runtime/src/host.rs` — `host_debug_string` の `Bytes` arm（`<bytes len=N>`）
- `crates/yulang/src/main.rs` — `format_runtime_vm_value` と `format_primitive_op` に bytes arm

**Native 側**:
- `crates/yulang-native/src/abi_lane.rs` — `NativeAbiRepr`/`NativeAbiValueLane` のマッチに bytes arm。`NativeRuntimePtrKind::Bytes` の追加は**今は未実装**で、bytes は暫定的に `NativeRuntimePtrKind::RuntimeValue` 扱いになってる
- `crates/yulang-native/src/cps_repr.rs` — `primitive_result_lane` に bytes arm
- `crates/yulang-native/src/cps_repr_cranelift.rs` — `NativeCpsI64HeapValue::Bytes(BytesTree)`、bytes helper 6 個、primitive codegen / validation の dispatch を追加
- `crates/yulang-native/src/cps_repr_cranelift/runtime_symbols.rs` — bytes helper symbol を登録
- `crates/yulang-native/src/cps_lower.rs` / `eval.rs` / `lower.rs` — linter が自動で arm を足してくれた
- `crates/yulang-wasm/src/output.rs` — `VmValue::Bytes` の fallback 表示を `<bytes len=N>` にした

### スモーク確認

VM / native で以下が動く:

```yu
my b: bytes = std::str::to_bytes "hello"
my n = std::bytes::len b
println n.show       -- "5"
my b2 = std::bytes::concat b b
println (std::bytes::len b2).show  -- "10"
```

### (3) `path` 型の追加

完了。`PrimitiveTypeFamily::Path`、`VmValue::Path(Rc<PathBuf>)`、`BytesToPath` / `PathToBytes` を追加し、VM と native effects の両方で `bytes -> path -> bytes` が動く。

Unix では `OsStringExt` / `OsStrExt` で raw bytes を保持する。非 Unix では `String::from_utf8_lossy` / `to_string_lossy` の fallback。

### (4) std での cast 宣言と path コンストラクタ

完了。

- `crates/yulang-sources/std/path.yu`
- `lib/std/path.yu`
- `crates/yulang-sources/src/stdlib.rs`
- `crates/yulang-wasm/std_sources_manifest.rs`
- `lib/std/prelude.yu`
- `crates/yulang-sources/std/prelude.yu`

`std::path::of_bytes` は明示関数、`path -> bytes` は `Cast path` impl で暗黙 cast される。

### (5) `bytes.to_utf8_raw`

完了。`BytesToUtf8Raw: bytes -> (str, int)` を追加し、VM と native effects の両方で valid UTF-8 prefix と valid byte count を返す。

`crates/yulang-sources/std/bytes.yu` / `lib/std/bytes.yu` も追加した。`bytes` に `len` / `concat` / `to_utf8_raw` / `to_utf8_lossy` method と `Index bytes int/range` を定義している。`Display` / `Debug` は足していない。

### (6) host fs primitive の改造

完了。`fs` act は path/range ベースへ移行。

```yu
pub act fs:
    pub read_at: (path, range) -> (int, str, range)
    pub write_at: (path, range, str) -> int
    pub exists: path -> bool
    pub is_file: path -> bool
    pub is_dir: path -> bool
```

host 側の `read_at` は指定範囲の bytes を読み、UTF-8 valid prefix を `str` として返し、valid range を返す。`write_at` は既存 bytes の指定範囲を `str.as_bytes()` で置き換える。`exists` / `is_file` / `is_dir` は path を受ける形に変更した。

旧 host request 名の `read_text` / `write_text` は互換のため `host.rs` 側に残している。ただし std API は新しい path/result ベース。

### (7) std::fs 派生の Yulang 側書き直し

完了。`crates/yulang-sources/std/fs.yu` / `lib/std/fs.yu` は以下の形。

- `fs_err` payload は `path`
- `read_at: path -> range -> result (str, range) fs_err`
- `write_at: path -> range -> str -> result unit fs_err`
- `read_text: path -> result str fs_err`
- `write_text: path -> str -> result unit fs_err`
- `read_text_or_throw`

`bytes.to_utf8_lossy` は `std::bytes` 側に置いた。`[warn]` / `[throw]` 付きの UTF-8 wrapper は未実装。

## 残タスク

- `bytes.to_utf8` の strict 版と、必要なら warning/effect 付き UTF-8 wrapper を設計する。
- `std::fs` の range 読み書きを bytes ベース API としてさらに整理する。現状の host 境界は `(int, str, range)` なので、非 UTF-8 全体を丸ごと Yulang 側へ返す設計にはまだなっていない。
- `path` の join / parent / components などは未追加。最小 primitive の `of_bytes` / `to_bytes` だけで通している。

## ハマりどころメモ

- `EMBEDDED_STD_FILES` と `crates/yulang-wasm/std_sources_manifest.rs` の **両方**を更新しないと wasm 側が壊れる
- `lib/std/*.yu` と `crates/yulang-sources/std/*.yu` は手動で同期する（YULANG_STD は基本後者の embed を install したものを使う）。普段の `cargo run` 時には `find_std_root_near` で `lib/std` が拾われるルートもあるけど、ユーザ環境では `YULANG_STD` が設定されているので install しないと反映されない
- 新しい `PrimitiveOp` variant を足すと、exhaustive match が **約 10 か所**でコケる: `vm/primitive.rs`（arity と apply）、`abi_lane.rs`、`cps_repr.rs`、`cps_repr_cranelift.rs`（3 か所: codegen / validation / lane）、`cps_lower.rs`、`lower.rs`、`eval.rs`、`yulang/src/main.rs`（`format_primitive_op`）。`cargo check` で網羅されるので、エラーを順に潰す
- linter (rustfmt?) が match 整形を勝手にやることがある。編集後に diff を見て意図通りか確認

## 動作確認コマンド

```bash
# 個別テスト
cargo test -q -p yulang-runtime bytes_tree

# 全体 build
cargo check -p yulang-sources -p yulang-runtime -p yulang-native -p yulang-infer -p yulang -p yulang-wasm

# install
cargo run -q -p yulang -- install std

# VM smoke
cargo run -q -p yulang -- run path/to/smoke.yu

# native smoke
cargo run -q -p yulang -- native --kind run path/to/smoke.yu
```

# Host / Filesystem TODO

目的: 通常のスクリプト向け host capability を安定して予測しやすいものにする。
ただし、playground を危険にしたり、すべての host が同じ機能を持つように見せたりしない。

設計参照:

- `notes/design/error-handling-plan.md`

## 現在の状態

- `std::console` は `print` / `println` を提供する。
- `std::fs` は最初の最小 native-host surface として存在する。
  - `read_text: str -> opt str`
  - `write_text: (str, str) -> bool`
  - `exists: str -> bool`
  - `is_file: str -> bool`
  - `is_dir: str -> bool`
- 正確な filesystem API は意図的に TODO のまま。
- native CLI / basic host は Rust `std::fs` 経由で `std::fs` request を処理する。
- wasm / playground は今のところ filesystem request を unresolved のまま残す。

## まず error handling

- `result` の安定化や `std::fs` 拡張より先に、`error` sugar を固める。
- `std::fs` は `error fs_err:` の暫定 prototype を持つ。
- 現在の `opt str` / `bool` 返り値は暫定として扱う。
- host capability failure を何として表すか決める。
  - typed error effects
  - structured host request failures
  - value-level `result`
  - impossible host / runtime state だけを表す traps

## Filesystem API の問い

- Yulang に本物の `path` 型が必要か、最初の安定 API では `str` で十分か。
- path helper は `std::path` と `std::fs` のどちらに置くか。
- 最初の path helper は何か。
  - join
  - dirname
  - basename
  - extension
  - normalize
  - absolute / relative checks
- `read_text` は UTF-8 を検証するか、先に binary bytes を露出するか。
- `write_text` は parent directories を作るか。
- overwrite / append は別関数にするか、option にするか。
- 最初の安定 slice にどの directory operation を入れるか。
  - `list_dir`
  - recursive walking
  - metadata
  - create / remove directory

## Capability policy

- native CLI の default behavior
- playground behavior
- 明示的な deny / allow list
- 将来の package / script sandboxing
- unsupported host capabilities に対する明確な diagnostics

## 最初の安定 slice 候補

- `path` decision.
- `error fs_err:` と host failure mapping の安定化。
- `read_text: path -> [fs; fs_err] str`
- `write_text: (path, str) -> [fs; fs_err] unit`
- `exists: path -> [fs] bool`
- `is_file: path -> [fs] bool`
- `is_dir: path -> [fs] bool`

これは候補にすぎない。暫定実装を public contract として扱わない。

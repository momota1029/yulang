# Host / Filesystem TODO

目的: 通常のスクリプト向け host capability を安定して予測しやすいものにする。
ただし、playground を危険にしたり、すべての host が同じ機能を持つように見せたりしない。

設計参照:

- `notes/design/error-handling-plan.md`

## File-backed str 案(2026-05-23編集)

ファイル編集 API は、`file_handle` 専用の操作を前面に出すよりも、
「隠蔽された `file_handle` を `str` 変数のように操作している」と見える形へ寄せる。
`file_handle` の実体は概念的には `(path, str)` だが、外側からはその組を直接見せない。
`file_handle` に `get` / `set` さえ定義できれば、既存の `str` 変数向け lens を
そのまま使える。

中心の考え方:

- `fs::read` / `fs::open` は、隠蔽型 `file_handle` の mutable ref を返す。
  - 型としては `ref<'[fs], file_handle>` だが、`file_handle` には `str` と同じ
    get / set surface を生やす。
  - 表面上は `str` 変数として読める。
  - `get(file_handle) -> str` は内部の text を返す。
  - `set(file_handle, str)` は内部の text を置き換えて dirty にする。
  - `replace` / `splice` / `lines` などの lens は `old = get(file)`、
    `new = str_operation(old)`、`set(file, new)` へ展開できる。
  - `[fs]` effect 解決時に、内部の `path` と現在の `str` を使って書き戻す。
- `str` の破壊的変換は、すべて `get` / `set` の上の lens として定義する。
  - append / insert / replace / delete は API として用意してよい。
  - `splice(range, replacement) -> removed_str` は、`get` した旧 `str` に対する
    pure splice と、`set` による置き換えで実装できる。
  - `range` は byte range ではなく書記素クラスタ range。
  - `str[range]` と同じ座標系を使う。
- `lines` は `str` surface 側に生やす。
  - `text.lines` は line view を返す。
  - line view は、元の get/set cell への lens として素直に実装する。
  - `file_handle` 専用の line view を作らず、通常の `str` lens を再利用する。
- `[fs]` effect の解決時に、dirty な `file_handle` の現在の `str` を backing file へ適用する。
  - 実際にファイルを開きっぱなしにするわけではない。
  - close は public API として持たない。
  - unresolved な `[fs]` のままなら、mock / test host では通常の `str` 編集として扱える。

想定 API の雰囲気:

```yu
my &text = fs::open "a.txt"

for line in text.lines:
  if line.starts_with "TODO":
    line[0..4] = "DONE"
```

このとき `line[0..4] = "DONE"` は:

1. `text.get()` で現在の `str` を読む
2. line view / local range を現在の `str` 上の書記素 range へ変換する
3. pure `str.splice` で新しい `str` と失われた `str` を作る
4. `text.set(new_text)` で内部の `str` を置き換える
5. 返り値は置換で失われた `str`

実装上の分担:

- `StringTree`
  - 書記素長、byte 長、改行数を node metadata として持つ。
  - `line_count` / `line_start` / `line_range` は書記素 range を返す。
- `file_handle`
  - 隠蔽型として `(path, str)` を持つ。
  - `get` / `set` を提供する。
  - `set` のたびに内部 `str` を更新し、dirty にする。
- line view
  - 作成時の line identity / range と、元の get/set cell への参照を持つ。
  - 書き込み時に `get` した現在の `str` で range を再解決し、`set` で戻す。
- fs host
  - effect 解決時に dirty な `file_handle` の `str` を path へ書き戻す。
  - 複数の `file_handle` が同じ path を編集した場合は、最初の安定版では guard しない。

未決:

- `fs::read` と `fs::open` の名前を分けるか。
  - 既存 `read_text` は互換 API として当面残す。
  - editable なものは `open_text` / `read` / `open` のどれを主名にするか決める。
- `line view` が、元 `str` の別 splice で削除済みになった場合の扱い。
  - trap / empty range / stale line error のどれにするか。
- `[fs]` effect 解決時の splice 適用順。
  - ひとつの editable string 内では記録順。
  - 同じ path を複数 editable string が持つ場合は未定義寄りでよい。

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

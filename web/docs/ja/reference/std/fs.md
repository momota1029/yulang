# `std::io::file`

`std::io::file` は、text ファイル操作、メタデータ、buffer を使ったテキスト編集を提供する。
ファイルシステムへのアクセスには host が処理する `file` effect を使い、操作の失敗には型付きの `io_err` effect を使う。

prelude は高水準 helper と型を re-export する。
多くの例では短い名前を使うが、range の例では同名の低水準 host operation と区別するため、`std::io::file::read_at` と `std::io::file::write_at` を完全修飾する。

## path

ファイル操作は `path` を受け取る。
`str` は `path` に widen されるため、文字列リテラルを直接渡せる。
bytes から明示的に path を作る場合は `std::text::path::of_bytes` を使う。

```yulang
my path: path = "/tmp/yulang-fs-path.txt"
write_text path "ready"
read_text path
```

## ファイル全体のテキスト

`read_text` は UTF-8 の text ファイル全体を読む。
`write_text` は text ファイル全体を作成または置換する。

```yulang
write_text "/tmp/yulang-fs-whole.txt" "alpha\nbeta\n"
my content = read_text "/tmp/yulang-fs-whole.txt"
content.say
```

シグネチャはそれぞれ `path -> [file, io_err] str` と `path -> str -> [file, io_err] unit` である。

host が無効な path または UTF-8 ではないファイル内容を報告すると、`read_text` は `io_err::invalid_path` を発火する。

## scope 付きテキスト編集

`text_with` は snapshot を読み、callback に渡し、callback が返した最終テキストを保存する。
callback は `(result, final_text)` を返し、`text_with` は `final_text` を保存して `result` を返す。

```yulang
write_text "/tmp/yulang-fs-scoped.txt" "draft"

my before = text_with "/tmp/yulang-fs-scoped.txt": \text0 ->
    my $buffer = text0
    &buffer = $buffer + "\nreviewed"
    (text0, $buffer)

(before, read_text "/tmp/yulang-fs-scoped.txt")
```

最後の式は `("draft", "draft\nreviewed")` になる。
effect によって callback が中断し、pair を返さなかった場合は store に到達しないため、元のファイルは変わらない。

シグネチャは `path -> (str -> ['e] ('a, str)) -> [file, io_err, 'e] 'a` である。

同じ path に対する重なった `text_with` 呼び出しは、それぞれ独立した snapshot を持つ。
各 callback が戻るときに保存するため、後に実行された store が優先される。

## handler の生存期間を使うテキスト参照

`text` は host が保持する buffer へ結び付いた可変テキスト参照を作る。
参照の作成時にファイルを読み、ファイルがない場合はその呼び出しで `io_err::not_found` を発火する。
ファイルを作成する必要がある場合は、先に `write_text` を使う。

```yulang
write_text "/tmp/yulang-fs-buffer.txt" "first"

my &buffer = text "/tmp/yulang-fs-buffer.txt"
&buffer = $buffer + "\nsecond"
$buffer
```

同じ path に対する `text` 参照は buffer を共有し、`file` handler の終了時に書き戻す。
native host では通常、プログラムの終了時に当たる。
handler の終了処理で起きた書き戻し失敗は、catch 可能な `io_err` ではなく `yulang.host-io-error` runtime エラーになる。

シグネチャは `path -> [file, io_err] ref '[file] str` である。

返された参照は `.lines` などの文字列参照操作を使える。
詳細は [`std::text::str`](./str) を参照。

## range 互換操作

`read_at` と `write_at` は、range の振る舞いが暫定的な互換操作として残っている。
現在の native host は range を無視するため、`read_at` はファイル全体を読んで要求された range をそのまま返し、`write_at` はファイル全体を置換する。

```yulang
write_text "/tmp/yulang-fs-range.txt" "abcdef"

my requested = range 1 3
my (read, returned) =
    std::io::file::read_at "/tmp/yulang-fs-range.txt" requested

std::io::file::write_at "/tmp/yulang-fs-range.txt" (range 2 4) "XY"
(read, returned, read_text "/tmp/yulang-fs-range.txt")
```

この例では `read` が `"abcdef"`、`returned` が `requested` と同じ値になり、最終的なファイルは `"XY"` になる。
ファイル全体を扱う場合は `read_text` と `write_text` を使い、この操作を byte range I/O に使わない。

シグネチャはそれぞれ `path -> range -> [file, io_err] (str, range)` と `path -> range -> str -> [file, io_err] unit` である。

## メタデータ

`meta` は `io_err` を発火せずに `file_meta` を返す。
存在しない path とアクセスを拒否された path は `file_kind` の値で表す。

```yulang
write_text "/tmp/yulang-fs-meta.txt" "abc"

my info = meta "/tmp/yulang-fs-meta.txt"
(
    info.kind,
    info.size,
    info.readonly,
    info.modified,
    exists "/tmp/yulang-fs-meta.txt",
    is_file "/tmp/yulang-fs-meta.txt",
    is_dir "/tmp/yulang-fs-meta.txt",
)
```

module から抜粋したメタデータ宣言は次のとおりである。

```yulang
pub enum file_kind =
    missing | denied | file | dir | symlink | other

pub struct file_meta {
    kind: file_kind,
    size: int,
    readonly: bool,
    modified: opt instant,
}
```

`exists` は `missing` と `denied` に対して false を返し、それ以外の kind に対して true を返す。
`is_file` と `is_dir` は、それぞれ対応する kind に対してだけ true を返す。

## エラー

テキスト helper は effect row を通じて `io_err` を発火する。
module から抜粋した宣言は次のとおりである。

```yulang
pub error io_err:
    not_found path
    denied path
    invalid_path path
    failed (path, str)
```

`not_found`、`denied`、`invalid_path` は対象の path を保持する。
`failed` は host のエラーメッセージも保持する。
`io_err::wrap` はエラー effect を `result` 値へ閉じる。

```yulang
my invalid =
    std::text::path::of_bytes (std::text::str::to_bytes "bad\0path")
my wrapped = io_err::wrap: read_text invalid

case wrapped:
    result::ok text -> text
    result::err err -> case err:
        io_err::invalid_path _ -> "invalid path"
        _ -> "other error"
```

`file` effect には引き続き host handler が必要である。
host capability がない場合は、`io_err` の操作失敗ではなく runtime の capability エラーになる。

## 低水準の `file` effect

`file` は公開 host act であり、シグネチャで使う effect 名でもある。
host が操作の失敗を報告できる operation は `result` 値を返す。
高水準 helper は、その `err` 値を `io_err` effect に変換する。

```yulang
my path: path = "/tmp/yulang-fs-low-level.txt"
my stored = file::store (path, "raw")
my loaded = file::load path
(stored, loaded)
```

| 操作 | シグネチャ | 役割 |
|---|---|---|
| `file::load path` | `path -> [file] result str io_err` | text ファイル全体を読む。 |
| `file::store (path, text)` | `(path, str) -> [file] result unit io_err` | text ファイル全体を作成または置換する。 |
| `file::meta path` | `path -> [file] file_meta` | `io_err` の結果を返さずにメタデータを読む。 |
| `file::ambient_touch path` | `path -> [file] result unit io_err` | `text` が使う buffer を読み込む。 |
| `file::ambient_get path` | `path -> [file] str` | touch 済みの `text` buffer を読む。 |
| `file::ambient_set (path, text)` | `(path, str) -> [file] unit` | touch 済みの `text` buffer を置換する。 |
| `file::read_at (path, range)` | `(path, range) -> [file] result (str, range) io_err` | 低水準の range 互換読み込み。 |
| `file::write_at (path, range, text)` | `(path, range, str) -> [file] result unit io_err` | 低水準の range 互換書き込み。 |

`ambient_*` operation は `text` の下で使う protocol を構成する。
touch していない path に対する `ambient_get` と `ambient_set` の直接呼び出しは、この protocol の外にある。
この場合に native host で起きた失敗は、`yulang.host-io-error` runtime エラーになる。

## 早見表

| 操作 | シグネチャ |
|---|---|
| `read_text path` | `path -> [file, io_err] str` |
| `write_text path text` | `path -> str -> [file, io_err] unit` |
| `text_with path f` | `path -> (str -> ['e] ('a, str)) -> [file, io_err, 'e] 'a` |
| `text path` | `path -> [file, io_err] ref '[file] str` |
| `std::io::file::read_at path range` | `path -> range -> [file, io_err] (str, range)` |
| `std::io::file::write_at path range text` | `path -> range -> str -> [file, io_err] unit` |
| `meta path` | `path -> [file] file_meta` |
| `exists path` | `path -> [file] bool` |
| `is_file path` | `path -> [file] bool` |
| `is_dir path` | `path -> [file] bool` |
| `io_err::wrap action` | `'a [io_err; 'e] -> ['e] result ('a, 'other \| io_err)` |

## 関連ページ

- [エラー](../errors)：`io_err`、`catch`、`wrap`
- [`std::text::str`](./str)：文字列参照と line view
- [`std::data::result`](./result)：値としての成功と失敗

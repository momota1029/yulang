# `text` の `bytes`、`char`、`config`、`path`

このページでは、`std::text::bytes`、`std::text::char`、`std::text::config`、`std::text::path` を扱う。
文字列操作は [`std::text::str`](./str) のページを参照。
`parser` API は対象外である。

## `std::text::bytes`

`bytes` は組み込みの不変な byte sequence 型である。
この `module` は、byte 単位の長さ、等値比較、連結、index、slice、UTF-8 `prefix` の decode を提供する。

```yulang
my b = std::text::str::to_bytes "hé"
my prefix = b[0..<1]
my invalid = (std::text::str::to_bytes "é")[0..<1]

(
    b.len,
    b.is_empty,
    std::text::bytes::eq b b,
    (b.concat b).len,
    b[0],
    prefix.to_utf8_lossy,
    invalid.to_utf8_raw,
)
```

結果は `(3, false, true, 6, 104, "h", ("", 0))` になる。
index と長さは Unicode の文字数ではなく、byte 数を使う。
範囲外の index または slice は実行時に失敗する。

`to_utf8_raw` は、有効な UTF-8 である最長の `prefix` と、その byte 数を返す。
`to_utf8_lossy` は `prefix` だけを返す。
置換文字を挿入せず、最初の不正な byte 以降を捨てる。

### 早見表

| 操作 | シグネチャ |
| --- | --- |
| `len(b)` / `b.len` | `bytes -> int` |
| `is_empty(b)` / `b.is_empty` | `bytes -> bool` |
| `eq(x, y)` | `bytes -> bytes -> bool` |
| `concat(x, y)` / `x.concat y` | `bytes -> bytes -> bytes` |
| `index_raw(b, i)` / `b[i]` | `bytes -> int -> int` |
| `index_range(b, r)` / `b[r]` | `bytes -> range -> bytes` |
| `to_utf8_raw(b)` / `b.to_utf8_raw` | `bytes -> (str, int)` |
| `to_utf8_lossy(b)` / `b.to_utf8_lossy` | `bytes -> str` |

## `std::text::char`

`char` は文字列の index が返す組み込みの文字型である。
`is_whitespace` は Unicode の空白分類を使う。
`is_punctuation` は ASCII の句読点を認識し、`is_word` は Unicode の英数字と `_` を受け入れる。

```yulang
my letter = "A"[0]
my space = " "[0]
my mark = "!"[0]
my underscore = "_"[0]

(
    std::text::char::eq letter "A"[0],
    letter.to_string,
    space.is_whitespace,
    mark.is_punctuation,
    underscore.is_word,
)
```

結果は `(true, "A", true, true, true)` になる。

### 早見表

| 操作 | シグネチャ |
| --- | --- |
| `eq(x, y)` | `char -> char -> bool` |
| `to_string(c)` / `c.to_string` | `char -> str` |
| `is_whitespace(c)` / `c.is_whitespace` | `char -> bool` |
| `is_punctuation(c)` / `c.is_punctuation` | `char -> bool` |
| `is_word(c)` / `c.is_word` | `char -> bool` |

## `std::text::config` <Badge type="warning" text="暫定" />

> **暫定：** この `module` は独自の小さな形式を定義し、INI dialect との互換性を約束しない。
> 形式と API は変わる可能性がある。

`config` は、順序を保った `list section` を格納する。
公開された `section` は `name: str` と `entries: list (str, str)` の `field` を持つ。
最初の header より前にある entry は、名前が `""` の section に入る。

`parser` は、line、section 名、key、value の前後にある空白を取り除く。
空行と、空白を除いた先頭文字が `#` の line は無視する。
`[name]` は section を開始し、ほかの line では最初の `=` が key と value を分ける。
不正な空でない line は、現在は無視される。
同じ section が繰り返されると同じ section へ追記し、検索では最後に一致した key を使う。

```yulang
my cfg = std::text::config::parse "
root = first
[app]
name = yulang
name = final
ignored line
# comment
"

(
    cfg.get "" "root",
    cfg.get "app" "name",
    cfg.sections,
)
```

2 個の検索結果は `just "first"` と `just "final"` になる。
`sections` は 2 個の `name` entry を source の順序で保持する。

`load` はファイルを読み、parse する。
次の実行可能な例は、先に入力ファイルを作る。

```yulang
my file_name = "/tmp/yulang-config-reference.ini"
std::io::file::write_text file_name "[app]\nname = yulang\n"

my cfg = std::text::config::load file_name
cfg.get "app" "name"
```

結果は `just "yulang"` になる。
ファイルのエラーは `std::io::file::io_err` `effect` として発火する。

### 早見表

| 操作 | シグネチャ |
| --- | --- |
| `section { name, entries }` | `{ name: str, entries: list (str, str) } -> section` |
| `parse(source)` | `str -> config` |
| `get(c, section_name, key)` / `c.get section_name key` | `config -> str -> str -> opt str` |
| `sections(c)` / `c.sections` | `config -> list section` |
| `load(path)` | `str -> [std::io::file::file, std::io::file::io_err] config` |

## `std::text::path`

`path` はファイル操作が使う組み込みの `path` 値である。
この `module` は `path` と `bytes` を相互に変換し、`Display` の `impl` は lossy UTF-8 text を使う。

```yulang
my raw = std::text::str::to_bytes "/tmp/yulang"
my p = std::text::path::of_bytes raw

(
    std::text::bytes::eq raw p.to_bytes,
    p.show,
)
```

結果は `(true, "/tmp/yulang")` になる。
不正な UTF-8 byte は `path` の構築時に置換されるため、その `path` を `bytes` に戻しても元の byte sequence は保たれない。

### 早見表

| 操作 | シグネチャ |
| --- | --- |
| `of_bytes_raw(b)` | `bytes -> path` |
| `of_bytes(b)` | `bytes -> path` |
| `to_bytes(p)` / `p.to_bytes` | `path -> bytes` |
| `p.show` | `path -> str` |

## 関連ページ

- [`std::text::str`](./str)：不変文字列と文字列操作
- [`std::io::file`](./fs)：`path` を受け取るファイル操作
- [文字列](../strings)：文字列構文、埋め込み、書式化
- [標準ライブラリ一覧](./)：すべての `module` の一覧

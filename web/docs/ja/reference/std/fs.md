# `std::fs`

`std::fs` は text 指向の filesystem helper を提供する。これらは
host-handled effect であり、native host は直接処理する。一方で browser /
Wasm host では filesystem request が unresolved のまま残ることがある。

prelude は `std::fs::*` を reexport するため、通常は `read_text`、`read_at`、
`open`、`fs_err` を `std::fs::` なしで書く。

## path

filesystem helper は `path` を受け取る。`str` は `path` に widen されるので、
文字列リテラルをそのまま渡せる。

```yulang
read_text "data.txt"

my path: path = "data.txt"
read_text path
```

bytes から明示的に path を作る必要がある場合は `std::path::of_bytes` を使う。

## text file 全体を読む

```yulang
my text = read_text "data.txt"
text.say
```

`read_text path` は file 全体を text として読み、`str` を返す。

型は概ね次の形になる。

```yulang
path -> [fs; fs_err] str
```

host error は `fs_err` として直接投げられる。API は `result` を返さない。
値として扱いたい境界では `fs_err::wrap` を使う。

```yulang
case fs_err::wrap: read_text "data.txt":
    result::ok text -> text
    result::err _ -> ""
```

## byte range を読む

```yulang
my (text, valid) = read_at "data.txt" (0..<1024)
```

`read_at path range` は byte range を読み、`(str, range)` を返す。返ってくる
range は、実際に UTF-8 text へ変換できた byte range である。要求した slice
が invalid UTF-8 の途中で終わる場合、`text` は最長の valid prefix になり、
`valid` はその prefix を指す。

host error は `read_text` と同じく `fs_err` として投げられる。

## text handle を開く

```yulang
{
    my &fh = open "data.txt"
    $fh
}
```

`open path` は text file を mutable な文字列参照として開く。`my &fh = ...`
で受け、`$fh` で現在の text を読み、`&fh = text` で buffer 全体を置き換える。
参照経由で書くと buffer は dirty になり、現在の host は underlying handle
state が drop されたときに dirty な file handle を flush する。

`open_in path do` は local wrapper 形である。

```yulang
my &fh = open_in "data.txt" do
    $fh
```

handle を `do` block の中に閉じ込めたいときに使う。

## line view

文字列参照には `.lines` があり、fold や `for` で使える。

```yulang
{
    my &fh = open "data.txt"
    for &line in &fh.lines:
        $line.say
}
```

各 `line` は開いた文字列への mutable view である。代入すると file buffer が
更新される。

```yulang
{
    my &fh = open "data.txt"
    for &line in &fh.lines:
        if $line == "old\n":
            &line[std::range::full()] = "new\n"
        else:
            ()
}
```

## error

```yulang
pub error fs_err:
    not_found path
    denied path
    invalid_path path
```

filesystem error は operation 名で捕まえる。

```yulang
catch read_text "data.txt":
    fs_err::not_found _, _ -> ""
    fs_err::denied _, _ -> ""
    text -> text
```

関数境界で open な error effect ではなく値が欲しい場合、`fs_err::wrap` で
同じ error effect を `result _ fs_err` に閉じられる。

## 早見表

| 操作 | シグネチャ |
|---|---|
| `read_text path` | `path -> [fs; fs_err] str` |
| `read_at path range` | `path -> range -> [fs; fs_err] (str, range)` |
| `write_text path text` | `path -> str -> [fs; fs_err] unit` |
| `write_at path range text` | `path -> range -> str -> [fs; fs_err] unit` |
| `open path` | `path -> [fs; fs_err] ref '[fs] str` |
| `open_in path f` | `path -> (ref '[fs] str -> [e] 'a) -> [fs; fs_err; e] 'a` |
| `exists path` | `path -> [fs] bool` |
| `is_file path` | `path -> [fs] bool` |
| `is_dir path` | `path -> [fs] bool` |

## 関連ページ

- [エラー](../errors) — `fs_err`、`catch`、`wrap`
- [`std::str`](./str) — 文字列 index、splice、line view
- [`std::result`](./result) — 値としての success / error

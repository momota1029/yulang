# 標準ライブラリ中核

よく使う標準ライブラリ surface をまとめる。
API はまだ変わる可能性がある。

## `std::data::list`

```yulang
[1, 2, 3].append [4]
[1, 2, 3].first
[1, 2, 3][1]
[1, 2, 3][1..<3]
```

list は `int` と `range` の `Index`、`Fold`、`+` 経由の `Add` を実装している。
主な helper は `empty`、`singleton`、`cons`、`uncons`、`map`、`filter`、`fold`、`rev`、`append`、`first`、`sort` である。

mutable list ref には `.push` もある。

## `std::data::range`

```yulang
0..<10
0..10
0..
..<10
..
```

range は値であり、`Fold` を実装している。
そのため `for` や `std::control::nondet::each` に渡せる。

## `std::text::str`

```yulang
"abc".len
"abcd"[1..<3]
"abcd".splice (range 1 3) "XY"
```

文字列は `int` と `range` の `Index`、および `.len` の `Len` を実装している。

## `std::data::result`

```yulang
ok 1
err "bad"
```

`result 'ok 'err` は `map`、`and_then`、`unwrap_or` を提供する。
prelude は `result`、`ok`、`err` を reexport するため、ユーザーコードでは通常 `std::data::result::` や `result::` を付けない。
これは値として返すための型で、filesystem API の主 surface にはまだ使われていない。

## `std::io::console`

```yulang
say "hello"
42.say
print "raw"
println "line"
eprintln "error line"
```

console output は host-handled effect である。
`say` / `.say` は `Display.show` の結果に改行を付けて出力する。
`print` / `println` は raw string を stdout へ書く。
`note` / `.note` / `eprint` / `eprintln` / `dd` は stderr を使う。
host-facing operation は `out`、`err`、`warn`、`die` の effect family に分かれており、通常の program は wrapper と role method を使う。

## `std::io::file`

```yulang
write_text "/tmp/yulang-core-whole.txt" "draft"
read_text "/tmp/yulang-core-whole.txt"

write_text "/tmp/yulang-core-scoped.txt" "draft"
text_with "/tmp/yulang-core-scoped.txt": \content ->
    (content, content + "\nreviewed")

write_text "/tmp/yulang-core-buffer.txt" "draft"
my &buffer = text "/tmp/yulang-core-buffer.txt"
$buffer
```

filesystem surface は text 指向である。
`read_text` は UTF-8 のファイル全体を読み、`write_text` はファイルを作成または置換する。
host error が起きた場合、どちらも effect row を通じて `io_err` を発火する。
`text_with` は callback が返した最終テキストを保存する。
`text` は host-backed な可変テキスト参照を返し、buffer は `file` handler の終了時に flush される。

読む API 全体は [`std::io::file`](./fs) を参照。

## Prelude の Role

主な prelude role は次の通り。

- `Eq`, `Ord`
- `Add`, `Sub`, `Mul`, `Div`
- `Len`
- `Display`, `Debug`
- `Cast`
- `LowerHex`, `UpperHex`

`+`、`==`、`.len`、`.show`、`.debug`、文字列埋め込みなどの role method は、これらの role を通して解決される。
標準の `Cast` role は暗黙の cast 宣言とは別の仕組みであり、暗黙の cast は専用の変換規則 table を使う。

# 標準ライブラリ中核

よく使う標準ライブラリ surface をまとめる。API はまだ変わる可能性がある。

## `std::data::list`

```yulang
[1, 2, 3].append [4]
[1, 2, 3].last
[1, 2, 3][1]
[1, 2, 3][1..<3]
```

list は `int` と `range` の `Index`、`Fold`、`+` 経由の `Add` を実装している。主な helper は `empty`、`singleton`、`cons`、`uncons`、`map`、`filter`、`fold`、`rev`、`append`、`first`、`last`、`sort` である。

mutable list ref には `.push` もある。

## `std::data::range`

```yulang
0..<10
0..10
0..
..<10
..
```

range は値であり、`Fold` を実装している。そのため `for` や `std::control::nondet::each` に渡せる。

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

`result 'ok 'err` は `map`、`and_then`、`unwrap_or` を提供する。prelude は `result`、`ok`、`err` を reexport するため、ユーザーコードでは通常 `std::data::result::` や `result::` を付けない。これは値として返すための型で、filesystem API の主 surface にはまだ使われていない。

## `std::io::console`

```yulang
say "hello"
42.say
print "raw"
println "line"
eprintln "error line"
```

console output は host-handled effect である。`say` / `.say` は
`Display.show` の結果に改行を付けて出力する。`print` / `println` は raw
string を stdout へ書く。`note` / `.note` / `eprint` / `eprintln` / `dd` は
stderr を使う。host-facing operation は `out`、`err`、`warn`、`die` の effect
family に分かれており、通常の program は wrapper と role method を使う。

## `std::io::file`

```yulang
read_text "data.txt"
read_at "data.txt" (0..<1024)
open "data.txt"
```

filesystem surface は text 指向である。`read_text` は `str` を返し、host
error は effect row の `io_err` として直接投げる。`read_at` は byte range
を読み、UTF-8 として valid な text prefix と valid range を返す。`open` は
host-backed な text reference を返し、dirty な buffer は handle state の
drop 時に flush される。

読む API 全体は [`std::io::file`](./fs) を参照。

## Prelude の Role

主な prelude role は次の通り。

- `Eq`, `Ord`
- `Add`, `Sub`, `Mul`, `Div`
- `Len`
- `Display`, `Debug`
- `Cast`
- `LowerHex`, `UpperHex`

`+`、`==`、`.len`、`.show`、`.debug`、文字列埋め込み、implicit cast などは、これらの role を通して解決される。

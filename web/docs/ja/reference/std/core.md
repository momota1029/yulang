# 標準ライブラリ中核

よく使う標準ライブラリ surface をまとめる。API はまだ変わる可能性がある。

## `std::list`

```yulang
[1, 2, 3].append [4]
[1, 2, 3].last
[1, 2, 3][1]
[1, 2, 3][1..<3]
```

list は `int` と `range` の `Index`、`Fold`、`+` 経由の `Add` を実装している。主な helper は `empty`、`singleton`、`cons`、`uncons`、`map`、`filter`、`fold`、`rev`、`append`、`first`、`last`、`sort` である。

mutable list ref には `.push` もある。

## `std::range`

```yulang
0..<10
0..10
0..
..<10
..
```

range は値であり、`Fold` を実装している。そのため `for` や `std::undet::each` に渡せる。

## `std::str`

```yulang
"abc".len
"abcd"[1..<3]
"abcd".splice (range 1 3) "XY"
```

文字列は `int` と `range` の `Index`、および `.len` の `Len` を実装している。

## `std::result`

```yulang
ok 1
err "bad"
```

`result 'ok 'err` は `map`、`and_then`、`unwrap_or` を提供する。prelude は `result`、`ok`、`err` を reexport するため、ユーザーコードでは通常 `std::result::` や `result::` を付けない。これは値として返すための型で、filesystem API の主 surface にはまだ使われていない。

## `std::console`

```yulang
say "hello"
42.say
"debug".print
"debug".println
println ["debug", "output"]
```

console output は host-handled effect である。`say` / `.say` は `Display.show` の結果に改行を付けて出力する。`print` / `.print` は `Debug.debug` の結果を改行なしで出力し、`println` / `.println` は `Debug.debug` の結果に改行を付けて出力する。host-facing operation は `print_native` / `println_native` で、通常の program は wrapper と role method を使う。

## `std::fs`

```yulang
fs::read_text "data.txt"
fs::write_text ("data.txt", "text")
fs::exists "data.txt"
```

filesystem surface は意図的に最小限で、まだ最終形ではない。`read_text` は `opt str` を返す。移行用の `read_text_or_throw` は `nil` を `fs_err::not_found` へ写す。browser / wasm host では filesystem request が unresolved のまま残る場合がある。

## Prelude の Role

主な prelude role は次の通り。

- `Eq`, `Ord`
- `Add`, `Sub`, `Mul`, `Div`
- `Len`
- `Display`, `Debug`
- `Cast`
- `LowerHex`, `UpperHex`

`+`、`==`、`.len`、`.show`、`.debug`、文字列埋め込み、implicit cast などは、これらの role を通して解決される。

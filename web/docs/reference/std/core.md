# Core Standard Library

This page lists commonly used standard-library surfaces. The exact API is still
evolving.

## `std::list`

```yulang
[1, 2, 3].append [4]
[1, 2, 3].last
[1, 2, 3][1]
[1, 2, 3][1..<3]
```

Lists implement `Index` for `int` and `range`, `Fold`, and `Add` through `+`.
Useful helpers include `empty`, `singleton`, `cons`, `uncons`, `map`, `filter`,
`fold`, `rev`, `append`, `first`, `last`, and `sort`.

Mutable list references also support `.push`.

## `std::range`

```yulang
0..<10
0..10
0..
..<10
..
```

Ranges are values and implement `Fold`, so they work with `for` and
`std::undet::each`.

## `std::str`

```yulang
"abc".len
"abcd"[1..<3]
"abcd".splice (range 1 3) "XY"
```

Strings implement `Index` for `int` and `range`, and `Len` through `.len`.

## `std::result`

```yulang
ok 1
err "bad"
```

`result 'ok 'err` provides `map`, `and_then`, and `unwrap_or`. The prelude
reexports `result`, `ok`, and `err`, so user code normally writes them without
`std::result::` or `result::` qualification. It is a value type; filesystem APIs
currently do not use it as their primary surface.

## `std::console`

```yulang
println "hello"
print "no newline"
```

Console output is a host-handled effect. `println` appends a newline.

## `std::fs`

```yulang
fs::read_text "data.txt"
fs::write_text ("data.txt", "text")
fs::exists "data.txt"
```

The filesystem surface is intentionally minimal and not final. `read_text`
returns `opt str`; the transitional `read_text_or_throw` maps `nil` to
`fs_err::not_found`. Browser/wasm hosts may leave filesystem requests
unresolved.

## Roles From The Prelude

Common prelude roles include:

- `Eq`, `Ord`
- `Add`, `Sub`, `Mul`, `Div`
- `Len`
- `Display`
- `Cast`
- `LowerHex`, `UpperHex`

Operators such as `+`, `==`, `.len`, interpolation, and implicit casts resolve
through these roles.

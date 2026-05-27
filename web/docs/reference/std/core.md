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
say "hello"
42.say
"debug".print
"debug".println
println ["debug", "output"]
```

Console output is a host-handled effect. `say` and `.say` print `Display.show`
output with a newline. `print` and `.print` print `Debug.debug` output without a
newline, while `println` and `.println` print `Debug.debug` output with a newline. The
host-facing operations are `print_native` and `println_native`; most programs
use the wrappers and role methods.

## `std::fs`

```yulang
read_text "data.txt"
read_at "data.txt" (0..<1024)
open "data.txt"
```

The filesystem surface is text-oriented. `read_text` returns `str` and raises
`fs_err` directly through the effect row on host errors. `read_at` reads a byte
range and returns the UTF-8-valid text prefix with the valid range. `open`
returns a host-backed text reference whose dirty buffer is flushed when the
handle state is dropped.

See [`std::fs`](./fs) for the full reading API.

## Roles From The Prelude

Common prelude roles include:

- `Eq`, `Ord`
- `Add`, `Sub`, `Mul`, `Div`
- `Len`
- `Display`, `Debug`
- `Cast`
- `LowerHex`, `UpperHex`

Operators such as `+`, `==`, `.len`, `.show`, `.debug`, interpolation, and
implicit casts resolve through these roles.

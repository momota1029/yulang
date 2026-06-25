# Core Standard Library

This page lists commonly used standard-library surfaces. The exact API is still
evolving.

## `std::data::list`

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

## `std::data::range`

```yulang
0..<10
0..10
0..
..<10
..
```

Ranges are values and implement `Fold`, so they work with `for` and
`std::control::nondet::each`.

## `std::text::str`

```yulang
"abc".len
"abcd"[1..<3]
"abcd".splice (range 1 3) "XY"
```

Strings implement `Index` for `int` and `range`, and `Len` through `.len`.

## `std::data::result`

```yulang
ok 1
err "bad"
```

`result 'ok 'err` provides `map`, `and_then`, and `unwrap_or`. The prelude
reexports `result`, `ok`, and `err`, so user code normally writes them without
`std::data::result::` or `result::` qualification. It is a value type; filesystem APIs
currently do not use it as their primary surface.

## `std::io::console`

```yulang
say "hello"
42.say
print "raw"
println "line"
eprintln "error line"
```

Console output is a host-handled effect. `say` and `.say` print `Display.show`
output with a newline. `print` and `println` write raw strings to stdout.
`note`, `.note`, `eprint`, `eprintln`, and `dd` use stderr. The host-facing
operations are grouped under the `out`, `err`, `warn`, and `die` effect
families; most programs use the wrappers and role methods.

## `std::io::file`

```yulang
read_text "data.txt"
read_at "data.txt" (0..<1024)
open "data.txt"
```

The filesystem surface is text-oriented. `read_text` returns `str` and raises
`io_err` directly through the effect row on host errors. `read_at` reads a byte
range and returns the UTF-8-valid text prefix with the valid range. `open`
returns a host-backed text reference whose dirty buffer is flushed when the
handle state is dropped.

See [`std::io::file`](./fs) for the full reading API.

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

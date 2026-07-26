# Core Standard Library

This page lists commonly used standard-library surfaces. The exact API is still
evolving.

## `std::data::list`

```yulang
[1, 2, 3].append [4]
[1, 2, 3].first
[1, 2, 3][1]
[1, 2, 3][1..<3]
```

Lists implement `Index` for `int` and `range`, `Fold`, and `Add` through `+`.
Useful helpers include `empty`, `singleton`, `cons`, `uncons`, `map`, `filter`,
`fold`, `rev`, `append`, `first`, and `sort`.

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
write_text "/tmp/yulang-core-whole.txt" "draft"
read_text "/tmp/yulang-core-whole.txt"

write_text "/tmp/yulang-core-scoped.txt" "draft"
text_with "/tmp/yulang-core-scoped.txt": \content ->
    (content, content + "\nreviewed")

write_text "/tmp/yulang-core-buffer.txt" "draft"
my &buffer = text "/tmp/yulang-core-buffer.txt"
$buffer
```

The filesystem surface is text-oriented. `read_text` reads a whole UTF-8 file,
and `write_text` creates or replaces one. Both raise `io_err` through the
effect row on host errors. `text_with` stores the final text returned by its
callback. `text` returns a host-backed mutable text reference whose buffer is
flushed when the `file` handler ends.

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
other role methods resolve through these roles. The standard `Cast` role is
separate from implicit cast declarations, which use their own conversion-rule
table.

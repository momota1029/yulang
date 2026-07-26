# Core Standard Library

This page lists commonly used standard-library surfaces. The exact API is still
evolving.

## `std::core::cmp`

```yulang
(1 == 1, 1 < 2, (3.0).ge 2.0)
```

`std::core::cmp` declares `Eq` and `Ord`. It supplies `Eq` implementations for
`int`, `float`, `frac`, `bool`, `str`, `char`, and `list int`, and `Ord`
implementations for `int`, `float`, and `frac`. Comparison operators from
`std::core::ops` call these role methods. See [Structs & Roles](../structs) for
the role and `impl` syntax rather than treating these declarations as a second
role system.

## `std::core::convert`

```yulang
my ratio: frac = 2
my decimal: float = ratio
(ratio, decimal)
```

`std::core::convert` declares the `Cast` role with its explicit `.cast` method.
The module also registers implicit conversions from `path` to `bytes`, `int`
to `frac`, `int` to `float`, and `frac` to `float`. These `cast`
declarations do not implement or call the `Cast` role. [Casts](../casts)
covers where the compiler inserts registered implicit conversions.

## `std::core::fmt`

```yulang
(42.show, "%#x{255}", (just "x").debug)
```

`std::core::fmt` declares the `Display` and `Debug` roles, the format
specification types, and the formatting functions used by string
interpolation. It provides standard implementations for primitives and common
container and tuple shapes. [Strings](../strings) documents format
specifications and how to define these roles for user types.

## `std::core::seq`

```yulang
("abc".len, [1, 2, 3].len, "".is_empty)
```

`std::core::seq` declares `Len` and `IsEmpty`. It implements `Len` for `str`
and `list`, and `IsEmpty` for `str`, `list`, and `bytes`; the free `len`
function forwards to `.len`. The [`std::data::list`](./list) and
[`std::text::str`](./str) pages document the sequence operations rather than
repeating the role API here.

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

The prelude re-exports `Eq` and `Ord` from `std::core::cmp`, `Cast` from
`std::core::convert`, `Display` and `Debug` from `std::core::fmt`, and `Len`
and `IsEmpty` from `std::core::seq`. Arithmetic roles and `LowerHex` and
`UpperHex` come from `std::num`. Operators such as `+` and `==`, sequence
methods such as `.len`, and formatting methods such as `.show` and `.debug`
resolve through those roles.

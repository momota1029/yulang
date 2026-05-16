# `std::str`

Immutable strings with `Index`, `Len`, `Add` (concatenation), `Display`, and
`Debug` support.

## Literals and concatenation

```yulang
"hello"
"hello, " + name
"" + 1.show + " items"
```

`+` on strings concatenates. The `Add` impl is the same role-based
mechanism as `+` on numbers; user code can call `xs.add ys` instead.

## Length

```yulang
"hello".len    // 5
```

`Len` is exposed via `.len`.

## Indexing and slicing

```yulang
my s = "yulang"

s[0]            // "y"
s[s.len - 1]    // "g"
s[1..<3]        // "ul"
s[..2]          // "yu"
s[2..]          // "lang"
```

Strings implement `Index` for both `int` (a one-character string) and `range`
(a substring).

## Splicing

```yulang
"abcd".splice (range 1 3) "XY"     // "aXYd"
```

`splice` returns a new string with the slice replaced. The original is
unchanged.

## Display and conversion

```yulang
1.show              // "1"
true.show           // "true"
(1.5).show          // "1.5"
[1, 2, 3].show      // "[1, 2, 3]"
["a", "b"].show     // "[a, b]"
```

`.show` resolves through the `Display` role. The prelude ships user-facing
`Display` impls for primitives, `unit`, `list`, `opt`, `result`, and common
tuple arities when their payloads also implement `Display`; user types gain one
through `error E:` (auto-generated) or by writing
`impl Display T: our v.show = ...`. Values that implement `Display` also get
`.say`, which prints `.show` with a newline.

For structural developer-facing output, use `.debug`:

```yulang
[1, 2, 3].debug      // "[1, 2, 3]"
(just "x").debug     // "just \"x\""
```

`.debug` resolves through the `Debug` role. The prelude provides impls for
primitives, `list`, `opt`, `result`, and common tuple arities when their
payloads also implement `Debug`. The basic runtime host also renders structural
fallbacks for records and longer tuples, which is what `yulang run` and the
playground use for inspection. Values that implement `Debug` also get `.print`
and `.println`, which print `.debug` without or with a newline.

## Quick reference

| Operation | Signature |
|---|---|
| `s.len` | `str -> int` |
| `s + t` / `s.add t` | `str -> str -> str` |
| `s[i]` | `str -> int -> str` (single-character string) |
| `s[r]` | `str -> range -> str` |
| `s.splice r t` | `str -> range -> str -> str` |
| `value.show` | `Display 'a => 'a -> str` |
| `value.debug` | `Debug 'a => 'a -> str` |
| `value.say` | `Display 'a => 'a -> [console] ()` |
| `value.print` | `Debug 'a => 'a -> [console] ()` |
| `value.println` | `Debug 'a => 'a -> [console] ()` |

## See also

- [`std::list`](./list) — list operations are often paired with strings
- [Strings](../strings) — string-specific syntax and patterns
- [Casts](../casts) — between strings and wrapper types

# `std::str`

Immutable strings with `Index`, `Len`, `Add` (concatenation), and `Display`
support.

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
[1, 2, 3].show      // "[1, 2, 3]" via Display impl when present
```

`.show` resolves through the `Display` role. Every primitive ships with a
default `Display` impl; user types gain one through `error E:` (auto-generated)
or by writing `impl Display T: our v.show = ...`.

## Quick reference

| Operation | Signature |
|---|---|
| `s.len` | `str -> int` |
| `s + t` / `s.add t` | `str -> str -> str` |
| `s[i]` | `str -> int -> str` (single-character string) |
| `s[r]` | `str -> range -> str` |
| `s.splice r t` | `str -> range -> str -> str` |
| `value.show` | `Display 'a => 'a -> str` |

## See also

- [`std::list`](./list) — list operations are often paired with strings
- [Strings](../strings) — string-specific syntax and patterns
- [Casts](../casts) — between strings and wrapper types

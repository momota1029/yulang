# Strings

Yulang's string type is `str`. Strings are UTF-8 text. Indexing and slicing use
Unicode scalar-value positions exposed by the standard library, not raw byte
offsets. The older name `string` is still accepted as an alias in some places,
but new code should prefer `str`.

## Literals

```yulang
"hello"
"a\nb\u{21}"
"""
line1
line2
"""
```

String literals support common escapes such as `\n` and Unicode escapes such as
`\u{1F600}`. Triple-quoted strings may span multiple lines.

## Interpolation

```yulang
my name = "yu"
"hello %{name}"
"n = %{12}"
"ok = %{true}"
```

Interpolation formats a value through the `Display` role. The standard prelude
provides `Display` impls for primitives, `list`, `opt`, `result`, and common
tuple arities when their payloads also implement `Display`.

Integer hex formatting is available through the lower- and upper-hex roles:

```yulang
"hex = %x{255}"
"HEX = %X{255}"
```

## Indexing And Slicing

```yulang
"aあ🙂"[1]          // "あ"
"aあ🙂z"[1..<3]     // "あ🙂"
"aあ🙂z"[range 1 3]
```

`str` implements `Index str int` and `Index str range`. Indexing works by
character position, not byte offset.

## Splicing

```yulang
"aあ🙂z".splice (range 1 3) "bc"  // "abcz"
```

`std::str::splice` and the `.splice` method replace a character range with new
text.

## Display and `.show`

```yulang
1.show              // "1"
true.show           // "true"
"text".show         // "text"
[1, 2, 3].show      // "[1, 2, 3]"
["a", "b"].show     // "[a, b]"
(just "x").show     // "just x"
```

`.show` is the canonical conversion to `str`. It resolves through the
`Display` role. The standard prelude supplies user-facing impls for primitives,
`unit`, `list`, `opt`, `result`, and common tuple arities. Strings are rendered
without quotes, so structural values that contain strings are meant for readable
output rather than lossless inspection. `Display` also provides `.say`, which
prints `.show` with a newline.

Define `Display` for a user type with the usual role machinery:

```yulang
impl Display point:
    our p.show = "(" + p.x.show + ", " + p.y.show + ")"
```

The result is what `point::show p` or `p.show` returns, and what `%{p}` in a
string template formats.

## Debug and `.debug`

```yulang
[1, 2, 3].debug      // "[1, 2, 3]"
(just "x").debug     // "just \"x\""
(1, true).debug      // "(1, true)"
```

`.debug` is the developer-facing rendering path. It resolves through the
`Debug` role. The standard prelude provides `Debug` impls for primitives,
`list`, `opt`, `result`, and common tuple arities when their payloads also
implement `Debug`. The basic runtime host also renders structural fallbacks for
records and longer tuples, so `yulang run` and the playground can inspect them
without adding one impl per shape. `Debug` also provides `.print` and
`.println`, which print `.debug` without or with a newline. Use `.show` /
`.say` for user-facing text and `.debug` / `.print` / `.println` for structural
values while inspecting programs.

## Comments

```yulang
// line comment

/* nested
   block comment */

-- doc line comment

---
doc block
---
```

`//` and `/* ... */` are ordinary comments. `--` and `--- ... ---` are
documentation comments and may be consumed by tooling.

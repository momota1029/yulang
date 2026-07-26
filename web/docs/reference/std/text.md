# Text Bytes, Characters, Config, and Paths

This page covers `std::text::bytes`, `std::text::char`,
`std::text::config`, and `std::text::path`. String operations remain on the
[`std::text::str`](./str) page, and the parser API is outside this page.

## `std::text::bytes`

`bytes` is the built-in immutable byte-sequence type. The module provides
byte-based length, equality, concatenation, indexing, slicing, and UTF-8
prefix decoding.

```yulang
my b = std::text::str::to_bytes "hé"
my prefix = b[0..<1]
my invalid = (std::text::str::to_bytes "é")[0..<1]

(
    b.len,
    b.is_empty,
    std::text::bytes::eq b b,
    (b.concat b).len,
    b[0],
    prefix.to_utf8_lossy,
    invalid.to_utf8_raw,
)
```

The result is `(3, false, true, 6, 104, "h", ("", 0))`. Indexes and lengths
count bytes, not Unicode characters. An out-of-range index or slice fails at
runtime.

`to_utf8_raw` returns the longest valid UTF-8 prefix and the number of valid
bytes. `to_utf8_lossy` returns that prefix alone; it drops the input from the
first invalid byte instead of inserting a replacement character.

### Quick reference

| Operation | Signature |
| --- | --- |
| `len(b)` / `b.len` | `bytes -> int` |
| `is_empty(b)` / `b.is_empty` | `bytes -> bool` |
| `eq(x, y)` | `bytes -> bytes -> bool` |
| `concat(x, y)` / `x.concat y` | `bytes -> bytes -> bytes` |
| `index_raw(b, i)` / `b[i]` | `bytes -> int -> int` |
| `index_range(b, r)` / `b[r]` | `bytes -> range -> bytes` |
| `to_utf8_raw(b)` / `b.to_utf8_raw` | `bytes -> (str, int)` |
| `to_utf8_lossy(b)` / `b.to_utf8_lossy` | `bytes -> str` |

## `std::text::char`

`char` is the built-in character type returned by string indexing.
`is_whitespace` uses Unicode whitespace classification, `is_punctuation`
recognizes ASCII punctuation, and `is_word` accepts Unicode alphanumeric
characters and `_`.

```yulang
my letter = "A"[0]
my space = " "[0]
my mark = "!"[0]
my underscore = "_"[0]

(
    std::text::char::eq letter "A"[0],
    letter.to_string,
    space.is_whitespace,
    mark.is_punctuation,
    underscore.is_word,
)
```

The result is `(true, "A", true, true, true)`.

### Quick reference

| Operation | Signature |
| --- | --- |
| `eq(x, y)` | `char -> char -> bool` |
| `to_string(c)` / `c.to_string` | `char -> str` |
| `is_whitespace(c)` / `c.is_whitespace` | `char -> bool` |
| `is_punctuation(c)` / `c.is_punctuation` | `char -> bool` |
| `is_word(c)` / `c.is_word` | `char -> bool` |

## `std::text::config` <Badge type="warning" text="Provisional" />

> **Provisional:** This module defines a small format of its own and makes no
> INI-dialect compatibility promise. Its format and API may change.

`config` stores an ordered `list section`. A public `section` has `name: str`
and `entries: list (str, str)` fields. Entries before the first header belong
to the section named `""`.

The parser trims lines, section names, keys, and values. Empty lines and lines
whose first non-whitespace character is `#` are ignored. `[name]` starts a
section, and the first `=` on another line separates its key from its value.
Malformed non-empty lines are currently ignored. Repeated sections append to
the same section, and lookup uses the last matching key.

```yulang
my cfg = std::text::config::parse "
root = first
[app]
name = yulang
name = final
ignored line
# comment
"

(
    cfg.get "" "root",
    cfg.get "app" "name",
    cfg.sections,
)
```

The two lookups return `just "first"` and `just "final"`. `sections` preserves
both `name` entries in source order.

`load` reads and parses a file. This complete example creates its input first:

```yulang
my file_name = "/tmp/yulang-config-reference.ini"
std::io::file::write_text file_name "[app]\nname = yulang\n"

my cfg = std::text::config::load file_name
cfg.get "app" "name"
```

The result is `just "yulang"`. File errors are raised as
`std::io::file::io_err` effects.

### Quick reference

| Operation | Signature |
| --- | --- |
| `section { name, entries }` | `{ name: str, entries: list (str, str) } -> section` |
| `parse(source)` | `str -> config` |
| `get(c, section_name, key)` / `c.get section_name key` | `config -> str -> str -> opt str` |
| `sections(c)` / `c.sections` | `config -> list section` |
| `load(path)` | `str -> [std::io::file::file, std::io::file::io_err] config` |

## `std::text::path`

`path` is the built-in path value used by filesystem operations. The module
converts it to and from `bytes`, and its `Display` implementation uses lossy
UTF-8 text.

```yulang
my raw = std::text::str::to_bytes "/tmp/yulang"
my p = std::text::path::of_bytes raw

(
    std::text::bytes::eq raw p.to_bytes,
    p.show,
)
```

The result is `(true, "/tmp/yulang")`. Invalid UTF-8 bytes are replaced while
constructing a path, so converting such a path back to bytes does not preserve
the original byte sequence.

### Quick reference

| Operation | Signature |
| --- | --- |
| `of_bytes_raw(b)` | `bytes -> path` |
| `of_bytes(b)` | `bytes -> path` |
| `to_bytes(p)` / `p.to_bytes` | `path -> bytes` |
| `p.show` | `path -> str` |

## See also

- [`std::text::str`](./str) — immutable strings and string operations
- [`std::io::file`](./fs) — filesystem operations that consume paths
- [Strings](../strings) — string syntax, interpolation, and formatting
- [Standard Library Catalogue](./) — the full module inventory

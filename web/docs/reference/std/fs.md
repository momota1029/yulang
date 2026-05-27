# `std::fs`

`std::fs` provides text-oriented filesystem helpers. They are host-handled
effects: native hosts handle them directly, while browser/Wasm hosts may leave
filesystem requests unresolved.

The prelude re-exports `std::fs::*`, so examples normally use `read_text`,
`read_at`, `open`, and `fs_err` without a `std::fs::` prefix.

## Paths

Filesystem helpers take `path`. A `str` value widens to `path`, so string
literals are accepted directly:

```yulang
read_text "data.txt"

my path: path = "data.txt"
read_text path
```

Use `std::path::of_bytes` when you need to build a path from bytes explicitly.

## Read a whole text file

```yulang
my text = read_text "data.txt"
text.say
```

`read_text path` reads the whole file as text and returns `str`.

Its type is roughly:

```yulang
path -> [fs; fs_err] str
```

Host errors are raised as `fs_err` directly. The API does not return a
`result`; use `fs_err::wrap` when you want a value-level result.

```yulang
case fs_err::wrap: read_text "data.txt":
    result::ok text -> text
    result::err _ -> ""
```

## Read a byte range

```yulang
my (text, valid) = read_at "data.txt" (0..<1024)
```

`read_at path range` reads a byte range and returns `(str, range)`.
The returned range is the byte range that was actually converted to UTF-8 text.
If the requested slice ends in the middle of invalid UTF-8, `text` is the
longest valid prefix and `valid` marks that prefix.

Host errors are raised as `fs_err`, the same as `read_text`.

## Open a text handle

```yulang
{
    my file: ref '[fs] str = open "data.txt"
    file.get()
}
```

`open path` opens a text file as `ref '[fs] str`. The reference reads from the
host-backed file buffer with `.get()`. Writes through the reference update the
buffer and mark it dirty; the current host flushes a dirty file handle when the
underlying handle state is dropped.

`open_in path f` is the local wrapper form:

```yulang
open_in "data.txt": \file -> file.get()
```

Use it when the handle should stay scoped to one callback-shaped operation.

## Line views

String references expose `.lines`, which can be folded or used in `for`.

```yulang
{
    my file: ref '[fs] str = open "data.txt"
    for line: ref _ str in file.lines:
        line.get().say
}
```

Each `line` is a mutable view into the opened string. Assigning through it
updates the file buffer:

```yulang
{
    my file: ref '[fs] str = open "data.txt"
    for line: ref _ str in file.lines:
        if line.get() == "old\n":
            line[std::range::full()] = "new\n"
        else:
            ()
}
```

## Errors

```yulang
pub error fs_err:
    not_found path
    denied path
    invalid_path path
```

Catch filesystem errors by operation name:

```yulang
catch read_text "data.txt":
    fs_err::not_found _, _ -> ""
    fs_err::denied _, _ -> ""
    text -> text
```

`fs_err::wrap` turns the same error effect into `result _ fs_err` when a
function boundary needs a value instead of an open error effect.

## Quick reference

| Operation | Signature |
|---|---|
| `read_text path` | `path -> [fs; fs_err] str` |
| `read_at path range` | `path -> range -> [fs; fs_err] (str, range)` |
| `write_text path text` | `path -> str -> [fs; fs_err] unit` |
| `write_at path range text` | `path -> range -> str -> [fs; fs_err] unit` |
| `open path` | `path -> [fs; fs_err] ref '[fs] str` |
| `open_in path f` | `path -> (ref '[fs] str -> [e] 'a) -> [fs; fs_err; e] 'a` |
| `exists path` | `path -> [fs] bool` |
| `is_file path` | `path -> [fs] bool` |
| `is_dir path` | `path -> [fs] bool` |

## See also

- [Errors](../errors) — `fs_err`, `catch`, and `wrap`
- [`std::str`](./str) — string indexing, splicing, and line views
- [`std::result`](./result) — value-level success/error results

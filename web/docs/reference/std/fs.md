# `std::io::file`

`std::io::file` provides text-oriented filesystem helpers. The module exposes a
host-handled `file` effect plus `io_err` errors for host failures. Native hosts
handle the operations directly, while browser/Wasm hosts may leave filesystem
requests unresolved.

The prelude re-exports `std::io::file::*`, so examples normally use `read_text`,
`read_at`, `open`, and `io_err` without a `std::io::file::` prefix.

## Paths

Filesystem helpers take `path`. A `str` value widens to `path`, so string
literals are accepted directly:

```yulang
read_text "data.txt"

my path: path = "data.txt"
read_text path
```

Use `std::text::path::of_bytes` when you need to build a path from bytes
explicitly.

## Read a whole text file

```yulang
my text = read_text "data.txt"
text.say
```

`read_text path` reads the whole file as text and returns `str`.

Its type is roughly:

```yulang
path -> [file, io_err] str
```

Host errors are raised as `io_err` directly. The API does not return a
`result`; use `io_err::wrap` when you want a value-level result.

```yulang
case io_err::wrap: read_text "data.txt":
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

Host errors are raised as `io_err`, the same as `read_text`.

## Open a text handle

```yulang
{
    my &fh = open "data.txt"
    $fh
}
```

`open path` opens a text file as a mutable string reference. Bind it with
`my &fh = ...`; then `$fh` reads the current text and `&fh = text` replaces the
buffer. Writes through the reference mark the buffer dirty; the current host
flushes a dirty file handle when the underlying handle state is dropped.

`open_in` takes a callback. With the [`do` notation](../application#do-callback-syntax), you write it like this:

```yulang
my &fh = open_in "data.txt" do
$fh
```

Use it when the handle should stay scoped to the callback.

## Line views

String references expose `.lines`, which can be folded or used in `for`.

```yulang
{
    my &fh = open "data.txt"
    for &line in &fh.lines:
        $line.say
}
```

Each `line` is a mutable view into the opened string. Assigning through it
updates the file buffer:

```yulang
{
    my &fh = open "data.txt"
    for &line in &fh.lines:
        if $line == "old\n":
            &line[std::data::range::full()] = "new\n"
}
```

## Errors

```yulang
pub error io_err:
    not_found path
    denied path
    invalid_path path
```

Catch filesystem errors by operation name:

```yulang
catch read_text "data.txt":
    io_err::not_found _, _ -> ""
    io_err::denied _, _ -> ""
    text -> text
```

`io_err::wrap` turns the same error effect into `result _ io_err` when a
function boundary needs a value instead of an open error effect.

## Quick reference

| Operation | Signature |
|---|---|
| `read_text path` | `path -> [file, io_err] str` |
| `read_at path range` | `path -> range -> [file, io_err] (str, range)` |
| `write_text path text` | `path -> str -> [file, io_err] unit` |
| `write_at path range text` | `path -> range -> str -> [file, io_err] unit` |
| `open path` | `path -> [file, io_err] ref '[file] str` |
| `open_in path f` | `path -> (ref '[file] str -> ['e] 'a) -> [file, io_err; 'e] 'a` |
| `exists path` | `path -> [file] bool` |
| `is_file path` | `path -> [file] bool` |
| `is_dir path` | `path -> [file] bool` |

## See also

- [Errors](../errors) — `io_err`, `catch`, and `wrap`
- [`std::text::str`](./str) — string indexing, splicing, and line views
- [`std::data::result`](./result) — value-level success/error results

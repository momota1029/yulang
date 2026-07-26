# `std::io::file`

`std::io::file` provides text file operations, metadata, and buffered text
edits. Filesystem access uses the host-handled `file` effect. Operation
failures use the typed `io_err` effect.

The prelude re-exports the high-level helpers and types. Most examples use
their short names. The range example qualifies `std::io::file::read_at` and
`std::io::file::write_at` to distinguish the helpers from the low-level host
operations with the same names.

## Paths

File operations take `path`. A `str` widens to `path`, so string literals can
be passed directly. Use `std::text::path::of_bytes` to construct a path from
bytes explicitly.

```yulang
my path: path = "/tmp/yulang-fs-path.txt"
write_text path "ready"
read_text path
```

## Whole-file text

`read_text` reads a whole UTF-8 text file. `write_text` creates or replaces a
whole text file.

```yulang
write_text "/tmp/yulang-fs-whole.txt" "alpha\nbeta\n"
my content = read_text "/tmp/yulang-fs-whole.txt"
content.say
```

Their signatures are `path -> [file, io_err] str` and
`path -> str -> [file, io_err] unit`, respectively.

`read_text` raises `io_err::invalid_path` when the host reports invalid path
data or file data that is not valid UTF-8.

## Scoped text edits

`text_with` reads a snapshot, passes it to a callback, and stores the final
text returned by that callback. The callback returns `(result, final_text)`;
`text_with` stores `final_text` and returns `result`.

```yulang
write_text "/tmp/yulang-fs-scoped.txt" "draft"

my before = text_with "/tmp/yulang-fs-scoped.txt": \text0 ->
    my $buffer = text0
    &buffer = $buffer + "\nreviewed"
    (text0, $buffer)

(before, read_text "/tmp/yulang-fs-scoped.txt")
```

The final expression is `("draft", "draft\nreviewed")`. If the callback exits
through an effect instead of returning the pair, the store is not reached and
the original file stays unchanged.

Its signature is
`path -> (str -> ['e] ('a, str)) -> [file, io_err, 'e] 'a`.

Overlapping `text_with` calls for the same path each keep their own snapshot.
Each callback stores on return, so the later store wins.

## Handler-extent text references

`text` creates a mutable text reference backed by a host buffer. It reads the
file when the reference is created, and a missing file raises
`io_err::not_found` at that call. Use `write_text` first when the file must be
created.

```yulang
write_text "/tmp/yulang-fs-buffer.txt" "first"

my &buffer = text "/tmp/yulang-fs-buffer.txt"
&buffer = $buffer + "\nsecond"
$buffer
```

The buffer is shared by `text` references to the same path and is written back
when the `file` handler ends. With the native host, that is normally program
exit. A write-back failure at handler discharge is a
`yulang.host-io-error` runtime error, not a catchable `io_err`.

Its signature is `path -> [file, io_err] ref '[file] str`.

The returned reference supports string reference operations such as
`.lines`; see [`std::text::str`](./str).

## Range compatibility operations

`read_at` and `write_at` remain as compatibility operations with provisional
range behavior. The current native host ignores the range: `read_at` reads the
whole file and returns the requested range unchanged, while `write_at`
replaces the whole file.

```yulang
write_text "/tmp/yulang-fs-range.txt" "abcdef"

my requested = range 1 3
my (read, returned) =
    std::io::file::read_at "/tmp/yulang-fs-range.txt" requested

std::io::file::write_at "/tmp/yulang-fs-range.txt" (range 2 4) "XY"
(read, returned, read_text "/tmp/yulang-fs-range.txt")
```

Here `read` is `"abcdef"`, `returned` equals `requested`, and the final file is
`"XY"`. Use `read_text` and `write_text` when whole-file behavior is intended;
do not rely on these operations for byte-range I/O.

Their signatures are `path -> range -> [file, io_err] (str, range)` and
`path -> range -> str -> [file, io_err] unit`, respectively.

## Metadata

`meta` returns `file_meta` without raising `io_err`. Missing and denied paths
are represented by `file_kind` values.

```yulang
write_text "/tmp/yulang-fs-meta.txt" "abc"

my info = meta "/tmp/yulang-fs-meta.txt"
(
    info.kind,
    info.size,
    info.readonly,
    info.modified,
    exists "/tmp/yulang-fs-meta.txt",
    is_file "/tmp/yulang-fs-meta.txt",
    is_dir "/tmp/yulang-fs-meta.txt",
)
```

The metadata declarations, excerpted from the module, are:

```yulang
pub enum file_kind =
    missing | denied | file | dir | symlink | other

pub struct file_meta {
    kind: file_kind,
    size: int,
    readonly: bool,
    modified: opt instant,
}
```

`exists` is false for `missing` and `denied`, and true for every other kind.
`is_file` and `is_dir` are true only for their matching kinds.

## Errors

Text helpers raise `io_err` through the effect row. Its declaration, excerpted
from the module, is:

```yulang
pub error io_err:
    not_found path
    denied path
    invalid_path path
    failed (path, str)
```

`not_found`, `denied`, and `invalid_path` carry the affected path. `failed`
also carries the host error message. `io_err::wrap` closes the error effect
into a `result` value.

```yulang
my invalid =
    std::text::path::of_bytes (std::text::str::to_bytes "bad\0path")
my wrapped = io_err::wrap: read_text invalid

case wrapped:
    result::ok text -> text
    result::err err -> case err:
        io_err::invalid_path _ -> "invalid path"
        _ -> "other error"
```

The `file` effect still requires a host handler. A missing host capability is a
runtime capability error rather than an `io_err` operation failure.

## Low-level `file` effect

`file` is the public host act and the effect name used in signatures. Its
operations return `result` values where the host can report an operation
failure. The high-level helpers turn those `err` values into the `io_err`
effect.

```yulang
my path: path = "/tmp/yulang-fs-low-level.txt"
my stored = file::store (path, "raw")
my loaded = file::load path
(stored, loaded)
```

| Operation | Signature | Role |
|---|---|---|
| `file::load path` | `path -> [file] result str io_err` | Read a whole text file. |
| `file::store (path, text)` | `(path, str) -> [file] result unit io_err` | Create or replace a whole text file. |
| `file::meta path` | `path -> [file] file_meta` | Read metadata without an `io_err` result. |
| `file::ambient_touch path` | `path -> [file] result unit io_err` | Load the buffer used by `text`. |
| `file::ambient_get path` | `path -> [file] str` | Read a touched `text` buffer. |
| `file::ambient_set (path, text)` | `(path, str) -> [file] unit` | Replace a touched `text` buffer. |
| `file::read_at (path, range)` | `(path, range) -> [file] result (str, range) io_err` | Low-level range compatibility read. |
| `file::write_at (path, range, text)` | `(path, range, str) -> [file] result unit io_err` | Low-level range compatibility write. |

The `ambient_*` operations form the protocol behind `text`. Calling
`ambient_get` or `ambient_set` on an untouched path is outside that protocol;
a native failure in that case is a `yulang.host-io-error` runtime error.

## Quick reference

| Operation | Signature |
|---|---|
| `read_text path` | `path -> [file, io_err] str` |
| `write_text path text` | `path -> str -> [file, io_err] unit` |
| `text_with path f` | `path -> (str -> ['e] ('a, str)) -> [file, io_err, 'e] 'a` |
| `text path` | `path -> [file, io_err] ref '[file] str` |
| `std::io::file::read_at path range` | `path -> range -> [file, io_err] (str, range)` |
| `std::io::file::write_at path range text` | `path -> range -> str -> [file, io_err] unit` |
| `meta path` | `path -> [file] file_meta` |
| `exists path` | `path -> [file] bool` |
| `is_file path` | `path -> [file] bool` |
| `is_dir path` | `path -> [file] bool` |
| `io_err::wrap action` | `'a [io_err; 'e] -> ['e] result ('a, 'other \| io_err)` |

## See also

- [Errors](../errors) — `io_err`, `catch`, and `wrap`
- [`std::text::str`](./str) — string references and line views
- [`std::data::result`](./result) — value-level success and error results

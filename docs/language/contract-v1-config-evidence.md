# Contract v1 Config Evidence

This page records evidence for the unstable `std::text::config` preview slice
under the [Standard API Contract](standard-api-contract.md). It is a ledger of
current executable evidence, not a roadmap.

## Executable Source

The source of truth is:

```text
tests/yulang/cases.toml
```

Current `standard-api` / `migration-canary` / `preview` / `config` manifest
coverage:

| kind | count | contract role |
| --- | ---: | --- |
| `run` | 3 | total parsing, lookup, raw section exposure, and file loading |
| total | 3 | text config preview slice |

The conformance command is:

```bash
cargo run -q -p yulang -- --std-root lib contract --contract config tests/yulang/cases.toml
```

Last recorded local validation on 2026-07-04:

```text
contract cases ok: 3
```

## Contracted Surface

The public surface is declared in `lib/std/text/config.yu`:

```yu
pub struct section { name: str, entries: list (str, str) }

pub type config with:
    struct self:
        sections_: list section

    pub c.get section_name key = std::text::config::get c section_name key
    pub c.sections = std::text::config::sections c

pub sections(c: config): list section
pub parse(source: str): config
pub get(c: config, section_name: str, key: str): opt str
pub load(path: str): [std::io::file::file, std::io::file::io_err] config
```

The `sections_` field is private implementation detail. The raw public escape
hatch is the method `c.sections`, plus the free function `sections(c)`.

## Contracted Semantics

`parse(source: str): config` is total and never fails. It currently fixes these
rules:

- blank lines are skipped after trimming;
- lines whose trimmed form starts with `#` are comments and skipped;
- `[name]` after trimming starts a section named `name`;
- entries before any section header belong to section `""`;
- `key = value` lines split on the first `=`;
- both key and value are trimmed after splitting, so mixed spacing is accepted;
- duplicate keys inside a section are last-wins for lookup;
- repeated same-name section blocks merge for lookup purposes;
- non-empty lines that are not headers, comments, or `=` entries are silently
  ignored.

Warning collection for ignored malformed lines is a future item. It is not part
of this contract slice.

## Stability

This is preview evidence only. The manifest cases intentionally carry
`migration-canary` and `preview`, not `stable-api`. The behavior above is the
current executable contract for the `config` tag, but public spelling can still
move in a later stabilization pass.

The policy mirrors the raw native TCP alpha wording: this evidence proves the
current slice through the public runner, but it does not stabilize adjacent
adapter details or final API shape.

## Non-Goals

This module is deliberately named `config`, not `ini`. It is not an INI dialect
and makes no dialect-compliance promise.

Type conversion stays with the user. Values are stored as `str`, so conversion
such as `.to_int` composes at the call site instead of being part of
`std::text::config`.

## Evidence Cases

`tests/yulang/cases.toml` includes these `config` runtime cases:

- `config_parse_basic` proves mixed spacing, comment and blank-line skipping,
  pre-header section `""`, named sections, duplicate-key last-wins lookup,
  ignored malformed lines, and the raw `c.sections` shape.
- `config_missing_lookup` proves missing keys and missing sections both return
  `nil`.
- `config_load_native` proves `load(path)` reads through the file effect row
  and then applies the same parser and lookup semantics to a temp file.

## Provenance / Decision Record

The design rulings came from the user on 2026-07-04, with Claude (Fable 5) as
the supervising author: total parse, honest not-INI naming, first-`=` splitting
with trimming, duplicate-key last-wins lookup, repeated same-name section blocks
merged for lookup, and the raw escape hatch spelling `c.sections`.

The same-name accessor pitfall is recorded here because it affected the final
implementation shape. Naming the public method `c.sections` while the private
struct field was also `sections` caused accessor self-recursion, so the private
field was renamed to `sections_`. The public spelling must remain `c.sections`.

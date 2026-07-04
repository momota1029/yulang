# Contract v1 Standard API Evidence

This page records evidence for
[Standard API Contract](standard-api-contract.md). It is a ledger of current
executable evidence, not a roadmap.

## Executable Source

The source of truth is:

```text
tests/yulang/cases.toml
```

Current `standard-api` / `stable-api` / `str` manifest coverage for String API
v1 and its stable ref/file-line interactions:

| kind | count | contract role |
| --- | ---: | --- |
| `run` | 11 | compact behavior for pure string APIs, method dispatch, ref mutation, and file-line string views |
| `public-signature` | 19 | exact pure and `ref '[e] str` public type projection |
| total | 30 | String API v1 executable slice |

The conformance command is:

```bash
cargo run -q -p yulang -- --std-root lib contract --contract standard-api --contract stable-api --contract str tests/yulang/cases.toml
```

Last recorded local validation on 2026-07-04:

```text
contract cases ok: 30
```

## String API v1

The manifest currently fixes these pure `std::text::str` signatures:

- `find`, `contains`, `starts_with`, `ends_with`;
- `split`, `split_once`, `join`;
- `trim`, `trim_start`, `trim_end`;
- `repeat`;
- `to_int`.

The `str_api_v1` runtime case fixes representative behavior for empty needles,
missing matches, split and split-once boundaries, joining empty and non-empty
lists, trimming whitespace, repeat counts at and below zero, signed integer
parsing, and method-form dispatch.

The `record_field_named_like_str_method` runtime case keeps record field access
and string method dispatch distinct when a record field has the same name as a
string method.

## Ref String Mutation Methods

The manifest fixes exact public signatures for:

- `replace_once!`;
- `replace!`;
- `replace_all!`;
- `splice!`;
- `trim!`;
- `trim_start!`;
- `trim_end!`.

Each mutating method is sugar for `update` on the receiver `ref '[e] str`. The
effect row is the receiver ref tail, not a hidden string-specific effect. The
signature canaries therefore require methods to print as `ref 'a str -> ... ->
['a] ()` and reject private stack evidence in the projected type.

The `ref_str_mutating_methods_local` runtime case proves the same public
receiver method path works over a local ref-shaped buffer for replace, trim, and
splice behavior.

## Parser Pattern P1/P2

The parser pattern contract is limited to case-arm patterns. It does not close
the full parser DSL as an ordinary expression language.

Current `parser-dsl` / `patterns` manifest coverage:

| kind | count | contract role |
| --- | ---: | --- |
| `run` | 1 | case-arm parser pattern behavior |
| `check` | 2 | malformed parser pattern diagnostics |
| `public-signature` | 1 | effect-hygiene public projection for a parser-pattern helper |
| total | 4 | Parser Pattern P1/P2 executable slice |

The conformance command is:

```bash
cargo run -q -p yulang -- --std-root lib contract --contract parser-dsl --contract patterns tests/yulang/cases.toml
```

Last recorded local validation on 2026-07-04:

```text
contract cases ok: 4
```

The closed subset covers:

- literal parser patterns in `case` arms;
- capture record binding from parser results;
- guards over captured fields;
- terminal rest `..` capture or discard;
- interpolation references inside rule literals.

The malformed subset covers non-terminal `..` and unsupported lazy quantifiers
such as `*?`. Full parser-expression execution, adapters, and the rest of the
parser DSL remain preview surface outside this slice.

## Closed Slice

The String API v1 slice is closed for the functions and ref methods listed on
this page. Additional string helpers should enter this evidence only after they
have focused runtime behavior or exact public-signature cases in
`tests/yulang/cases.toml`.

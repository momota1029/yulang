# Contract v1 Standard API Evidence

This page records evidence for
[Standard API Contract](standard-api-contract.md). It is a ledger of current
executable evidence, not a roadmap.

## Executable Source

The source of truth is:

```text
tests/yulang/cases.toml
```

## Result And Error Helpers

Current `standard-api` / `stable-api` / `result` manifest coverage:

| kind | count | contract role |
| --- | ---: | --- |
| `run` | 7 | compact behavior for result helpers and error wrapping into result values |
| `public-signature` | 3 | exact result helper public type projection |
| total | 10 | Result API executable slice |

The result conformance command is:

```bash
cargo run -q -p yulang -- --std-root lib contract --contract standard-api --contract stable-api --contract result tests/yulang/cases.toml
```

Last recorded local validation on 2026-07-06:

```text
contract cases ok: 10
```

Current `standard-api` / `stable-api` / `errors` manifest coverage:

| kind | count | contract role |
| --- | ---: | --- |
| `run` | 10 | compact behavior for generated user error helpers and stable `io_err` integration |
| `public-signature` | 8 | exact generated error helper and constructor public type projection |
| total | 18 | Generated error helper executable slice |

The error helper conformance command is:

```bash
cargo run -q -p yulang -- --std-root lib contract --contract standard-api --contract stable-api --contract errors tests/yulang/cases.toml
```

Last recorded local validation on 2026-07-06:

```text
contract cases ok: 18
```

Current `errors` / `from` / `up` manifest coverage:

| kind | count | contract role |
| --- | ---: | --- |
| `run` | 4 | explicit and automatic upcast behavior, plus no-`from` mismatch preservation |
| `public-signature` | 1 | exact generated `up` public type projection |
| total | 5 | Error upcast executable slice |

The focused upcast conformance command is:

```bash
cargo run -q -p yulang -- --std-root lib contract --contract errors --contract from --contract up tests/yulang/cases.toml
```

Last recorded local validation on 2026-07-06:

```text
contract cases ok: 5
```

The key error/result cases in `tests/yulang/cases.toml` are:

- `error_wrap_fail`;
- `error_from_wrap`;
- `error_up_wrap`;
- `error_auto_up_annotation`;
- `error_auto_up_row_var_unchanged`;
- `error_auto_up_no_from_diagnostic`;
- `error_display`;
- `error_display_from_wrap`;
- `user_error_wrap_public_signature`;
- `user_error_from_wrap_public_signature`;
- `user_error_up_public_signature`.

This slice protects the generated `error` helper surface: `fail`, `wrap`,
explicit `up`, generated `from` casts, generated display behavior, and result
conversion. The `error_auto_up_annotation` case fixes the automatic
annotation-boundary upcast rule: a concrete inner error effect may satisfy a
concrete annotated outer error effect when a generated `from` relationship
registered that conversion. `error_up_wrap` keeps the explicit `E::up` form
valid, and `user_error_up_public_signature` fixes its projected public type.

The negative side is part of the contract. `error_auto_up_no_from_diagnostic`
must continue to reject the same shape when no generated `from`/cast relation
exists. `error_auto_up_row_var_unchanged` keeps abstract row-variable/tail
behavior unchanged; automatic upcast is not attempted for row variables and is
not a global effect-row unification rule.

Current `standard-api` / `stable-api` / `str` manifest coverage for String API
v1 and its stable ref/file-line interactions:

| kind | count | contract role |
| --- | ---: | --- |
| `run` | 18 | compact behavior for pure string APIs, method dispatch, ref mutation, and file-line string views |
| `public-signature` | 19 | exact pure and `ref '[e] str` public type projection |
| total | 37 | String API v1 executable slice |

The conformance command is:

```bash
cargo run -q -p yulang -- --std-root lib contract --contract standard-api --contract stable-api --contract str tests/yulang/cases.toml
```

Last recorded local validation on 2026-07-06:

```text
contract cases ok: 37
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
| `run` | 2 | case-arm parser pattern behavior |
| `check` | 2 | malformed parser pattern diagnostics |
| `public-signature` | 2 | effect-hygiene public projection for parser-pattern helpers |
| total | 6 | Parser Pattern P1/P2 executable slice |

The conformance command is:

```bash
cargo run -q -p yulang -- --std-root lib contract --contract parser-dsl --contract patterns tests/yulang/cases.toml
```

Last recorded local validation on 2026-07-06:

```text
contract cases ok: 6
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

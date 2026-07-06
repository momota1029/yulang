# Standard API Contract

This page defines the current executable contract slices for stable standard
library APIs that are not part of the narrower Contract v0 stable core.

The executable source of truth is
[`tests/yulang/cases.toml`](../../tests/yulang/cases.toml). Cases tagged
`standard-api` and `stable-api` are compatibility promises for the named API
area. Cases tagged `migration-canary` prove current behavior without turning
that shape into a long-term compatibility promise.

[`contract-v1-standard-api-evidence.md`](contract-v1-standard-api-evidence.md)
records the current evidence for these slices.
[`contract-v1-config-evidence.md`](contract-v1-config-evidence.md) records the
unstable `std::text::config` preview slice.

## Result And Generated Error Helpers

The stable `std::data::result` slice covers the public `result` type and helper
functions such as `map`, `and_then`, and `unwrap_or`.

Generated `error E:` declarations are part of the same stable API boundary. A
public error declaration generates:

- the error value type and matching effect operations;
- `fail`, which raises a constructed error value through the error effect;
- `E::wrap`, which closes `E` and any `from`-registered narrower errors into a
  `result`;
- `E::up`, which explicitly handles narrower `from`-registered errors and
  re-raises them as `E`;
- generated `Cast Inner -> E` rules for each `from Inner` variant;
- generated `Display E` behavior for the declared error shape.

The contract also covers automatic annotation-boundary upcast for
`from`-registered error relationships. When the checker compares an inferred
effect row against a declared or annotated effect row, a concrete error effect
atom such as `Inner` may satisfy a concrete annotated atom such as `Outer` if
the generated `from` relationship registered a cast from `Inner` to `Outer`.
This is the implicit form of the explicit `Outer::up` boundary.

The conversion is intentionally local and narrow:

- only concrete effect atoms are considered for conversion;
- effect row variables and row tails pass through unchanged, and no conversion
  is attempted for them;
- a missing `from`/cast relationship remains a normal effect mismatch rather
  than silently passing;
- this rule applies at each declared or annotated boundary and is not a global
  effect-unification mechanism.

## String API v1

The `std::text::str` v1 slice covers these pure string functions and their
method forms where present:

- `find`, `contains`, `starts_with`, `ends_with`;
- `split`, `split_once`, `join`;
- `trim`, `trim_start`, `trim_end`;
- `repeat`;
- `to_int`.

`find` returns `opt range`. Empty needles match at byte position zero. `split`
with an empty separator returns the original source as one part. `split_once`
returns `nil` when the separator is not found and returns the prefix/suffix pair
for the first match otherwise. `to_int` accepts optional `+` / `-` signs and
ASCII decimal digits without trimming whitespace.

The mutating `ref '[e] str` method family is part of the same stable slice:

- `replace_once!`, `replace!`, `replace_all!`;
- `splice!`;
- `trim!`, `trim_start!`, `trim_end!`.

These methods are sugar for `update` on the receiver ref. They do not introduce
a separate host effect or hidden mutation channel. The public type therefore
exposes the receiver effect row tail: a receiver of type `ref 'e str` produces a
method effect row `['e] ()`.

## Manifest Policy

Standard API cases use these contract tags:

- `standard-api` for the public standard library surface;
- exactly one of `stable-api` or `migration-canary`;
- a narrower API area tag such as `str`, `config`, `result`, `path`, `time`,
  `file`, or `network`;
- `public-signature` for exact exported type projection;
- `runtime` for compact runtime behavior.

Public signature cases reject private inference evidence and placeholder-like
fragments such as `#...`, `AllExcept(...)`, `Unknown`, and accidental `Any`.

# Error Handling Plan

This note defines the work that should happen before stabilizing a `result`
type or expanding `std::fs`.

The immediate goal is not to add one more error container. It is to decide which
failures belong to diagnostics, which belong to host requests, and which should
be ordinary program values.

## Why Before `result`

`result` is only useful once the language knows what should be recoverable.
Without that boundary, filesystem APIs will accidentally encode policy choices
in ad hoc return types such as `opt str` or `bool`.

Examples:

- `read_text` missing file can be a recoverable value.
- `read_text` permission denied may need structured host error information.
- malformed source is a compiler diagnostic, not a runtime value.
- an unhandled host capability in the playground is a host/capability error, not
  a filesystem value.
- runtime invariant violations are bugs and should not become user-level
  `result`.

## Error Categories

### Compiler Diagnostics

These are produced before executable runtime behavior exists.

- parse errors;
- unresolved names and imports;
- type errors;
- missing/ambiguous role impls;
- unsupported lowering/runtime IR shapes;
- residual polymorphism that reaches runtime lowering/monomorphize.

Required shape:

- source span when available;
- compact message;
- structured kind for playground display;
- no VM/monomorphize internals in ordinary user messages.

### Runtime Traps

These are program execution failures that cannot continue safely.

Examples:

- VM invariant violation;
- invalid primitive input that should have been prevented by typing;
- impossible pattern/runtime shape mismatch;
- malformed compiled artifact that reaches execution.

Required shape:

- structured runtime error kind;
- optional source/runtime symbol context;
- clear distinction from user-recoverable errors.

### Host Capability Errors

These happen at the boundary between Yulang and the host.

Examples:

- filesystem permission denied;
- file not found;
- unsupported filesystem in wasm/playground;
- unavailable stdin;
- network denied by capability policy.

Required shape:

- operation path such as `std::fs::fs::read_text`;
- host-independent category;
- host detail string kept optional and non-semantic;
- capability-denied vs operation-failed distinction.

### Recoverable Program Values

These are expected failures that user programs should branch on.

Candidates:

- `result ok err`;
- `opt` only when failure has no useful detail;
- domain-specific enums.

Required shape:

- stable constructors;
- convenient pattern matching;
- no hidden host policy in constructor choice.

## Named-Catch Principle

Every error catch site names the error family it is handling. There is no
type-erased catch-all, and there is no runtime dispatch over arbitrary
`Display` instances. This is the single rule that keeps the rest of the design
small:

- Error effects always appear in signatures with concrete names.
- Aggregation across narrower families is explicit through `from` entries on
  the wider `error` declaration; the generated `wrap` and `up` helpers carry
  out the conversion.
- `Display` impls are auto-generated for `error E:` so that named catches can
  present the error without needing type erasure.

The convenience cost of giving up an anyhow-style boundary is real, but it
preserves the main property of the effect-row type system: every error has a
visible origin and a visible handler.

## Proposed Direction: Typed Error Effects

The leading candidate is a thiserror-like surface encoded with ordinary data
types and ordinary effects:

- each error family has a concrete algebraic data type;
- the same error family has a corresponding effect/act;
- each error constructor is also an effect operation;
- failing with a data value is provided through generated `fail` support;
- APIs expose the concrete error type in their effect row;
- callers peel errors by handling that effect;
- larger API boundaries aggregate errors through explicit `from` entries, casts,
  and optional aggregation handlers.

This keeps the error type visible in signatures while preserving Yulang's
effect-row subtraction model.

Sketch source:

```text
error fs_err:
  not_found path
  denied path
  invalid_path str

read_text: path -> [fs; fs_err] str
```

Desugaring:

```text
enum fs_err =
  not_found path
| denied path
| invalid_path str

act fs_err:
  not_found: path -> never
  denied: path -> never
  invalid_path: str -> never

impl Throw fs_err:
  type throws = '[fs_err]
  our e.throw = case e:
    fs_err::not_found path  -> fs_err::not_found path
    fs_err::denied path     -> fs_err::denied path
    fs_err::invalid_path s  -> fs_err::invalid_path s

impl Display fs_err:
  our e.show = case e:
    fs_err::not_found path  -> "file not found: " + path
    fs_err::denied path     -> "permission denied: " + path
    fs_err::invalid_path s  -> "invalid path: " + s
```

The user-facing throw is a prefix operator:

```text
fail fs_err::not_found path
```

`fail` is defined in `std::prelude` as a transparent wrapper over the `Throw`
role method:

```text
pub prefix(fail) = \e -> e.throw
```

This keeps detailed error construction direct without forcing receiver-heavy
spelling such as `(fs_err::not_found path).fail`.

The `Throw 'e` role exposes an associated effect row:

```text
pub role Throw 'e:
  type throws
  our e.throw: [throws] never
```

The associated `throws` row is what keeps `fail` honest. Without it the role
declaration's `ret_eff` collapses to empty, and `\e -> e.throw` silently loses
the effect of the impl body. With `throws` as an associated row, generic uses
such as `fail` carry the impl's effect row out to the call site.

The important point is that operation names mirror constructor names. This
makes handlers direct:

```text
catch read_text path:
  fs_err::not_found path, _ -> fallback
  fs_err::denied path, _ -> ...
```

`error` is a reserved word for this sugar.

Current prototype note:

- `std::fs` uses `error fs_err:` to define both the data constructors and
  same-name effect operations.
- `variant from source_type` parses as a single-payload wrapper variant for
  both `enum` and `error`, and lowering generates the corresponding
  `Cast source_type -> enum_type` implementation.
- Runtime lowering keeps constructor values and effect operations distinct
  by context: value construction lowers as an ordinary binding, while an
  effectful expected callee lowers as an effect operation.
- `result ok err` exists in `std::result` as a value container for
  effectful computations that are intentionally closed into values.
- `std::fs` no longer carries a manual `Throw fs_err` shim; `Throw fs_err` is
  generated from the `error fs_err:` declaration.
- `read_text_or_throw` is a transitional checked API. The host request still
  collapses all read failures to `opt::nil`, so it maps `nil` conservatively to
  `fs_err::not_found` until host requests can return typed filesystem errors.

Outstanding work for the throw side:

- `Throw 'e` role needs the associated `throws` row. Currently the role
  declaration in `std/error.yu` lowers `ret_eff` to the empty row, which clamps
  the throw effect to empty at the role level. The synthesized impl stores its
  own frozen scheme with the right effect atom, so the concrete `error E:`
  path happens to propagate effects, but generic uses like
  `\e -> e.throw` lose the effect through role resolution.
- Once the role carries an associated effect row, the prelude can switch from
  the identity placeholder to the real definition:

  ```text
  pub prefix(fail) = \e -> e.throw
  ```

  At call sites where `e` has a concrete error type, the transparent operator
  wrapper expands and the impl's `throws` row flows out, the same way
  `std::ops` operator wrappers expose concrete role methods today.

Anyhow-style aggregation is intentionally not in scope:

- A single open error namespace would erase the concrete error type and
  require runtime dispatch on `Display`. That cost loses the main benefit of
  effect-row typing: knowing where each error is raised and caught.
- All catching is done by name. Aggregation across narrower error families is
  expressed through explicit `from` entries on the wider `error` declaration
  and through `E::wrap` / `E::up`, not through a type-erased `any_err`.

Script-level convenience names should stay separate from typed error effects:

- `die`: unrecoverable panic/trap-like termination;
- `warn`: warning/log effect;
- `say`: stdout line output;
- `fail err`: recoverable typed error effect;
- `reject`: non-deterministic branch rejection in `std::undet`.

Aggregation remains explicit. The `from` entry is not limited to `error`
sugar: ordinary enum variants should be able to request the same generated
`Cast` implementation when the variant has exactly one payload.

```text
error io_err:
  fs from fs_err
  parse from parse_err
```

This should create an enum-like wrapper and make casts work first:

```text
enum io_err =
  fs fs_err
| parse parse_err

impl Cast fs_err:
  type to = io_err
  our e.cast = io_err::fs e

impl Cast parse_err:
  type to = io_err
  our e.cast = io_err::parse e
```

Each `error E:` declaration generates two helpers in `E`'s companion module:

- `E::wrap`: closes the error effect into a value. With `from` entries it
  catches the wider error effect together with all `from`-linked narrower
  error effects in one pass and returns `result ok E`. The `err` side carries
  the concrete `E` ADT, which is `Display` via the auto-generated impl.

  ```text
  io_err::wrap:
    (() -> [io_err; fs_err; parse_err; e] a) -> [e] result a io_err
  ```

- `E::up`: lifts narrower errors into the wider error effect. It catches
  `from`-linked narrower error effects and rethrows them as `E` through the
  corresponding wrapper constructor. Equivalent to running `E::wrap` and
  re-throwing the `err` side, but written as a single handler so users don't
  have to peel the result manually.

  ```text
  io_err::up:
    (() -> [io_err; fs_err; parse_err; e] a) -> [io_err; e] a
  ```

`up` is the everyday spelling for "let narrower errors bubble up as `E`":

```text
my read_and_parse path =
  io_err::up:
    let text = fs::read_text_or_throw path  // throws [fs_err]
    parse_json text                          // throws [parse_err]
  // the block's effect row is [io_err; ...]
```

This is the "thiserror-like" path: concrete error enums are the public
boundary, errors are carried, peeled, and aggregated by effects, and the
generated `Display E` impl lets `E::wrap` produce a user-presentable value
without losing the concrete type.

## Alternatives

### Global `err` Act

Sketch:

```text
act err 'e:
  raise: 'e -> never
```

This is simple and pairs naturally with `result`, but it risks making all
errors feel like one global effect and weakens the existing effect-row
subtraction story. Keep it as a fallback idea, not the first choice.

### Result-First APIs

Sketch:

```text
enum result 'ok 'err =
  ok 'ok
| err 'err

read_text: path -> [fs] result str file_error
```

This can still be useful as a helper boundary, especially when exporting an
effectful computation as a value. It should not be the primary mechanism until
error effects are understood.

### Host Error Enum Only

Sketch:

```text
enum host_error =
  unsupported str
| denied str
| not_found str
| failed str
```

This is still useful internally at host boundaries, but it is too broad as the
main language-level error model. Prefer concrete error families that can later
be aggregated explicitly.

## Current Provisional State

`std::fs` currently exposes:

```text
read_text: str -> opt str
read_text_or_throw: str -> [fs_err] str
write_text: (str, str) -> bool
exists: str -> bool
is_file: str -> bool
is_dir: str -> bool
error fs_err:
  not_found str
  denied str
  invalid_path str
impl Throw fs_err
```

This is intentionally minimal and unstable. It proves host effect plumbing,
same-name constructor/operation lowering, and basic native CLI behavior. Native
host errors are not typed yet, so `read_text_or_throw` still uses `not_found` as
the conservative `nil` mapping. It should not be documented as stable.

## Implementation Phases

### Phase 1: Error Taxonomy

- Add a small shared vocabulary for user-facing error categories.
- Map existing compiler/runtime errors into this vocabulary for display.
- Keep internal error enums richer than user-facing messages.

Success condition:

- Playground can distinguish compiler diagnostic, runtime trap, unhandled host
  request, and recoverable value.

### Phase 2: Host Error Values

- Add a concrete filesystem error family, likely through `error fs_err: ...`
  sugar once that sugar is designed.
- Define the corresponding enum, per-error act, and `Throw` surface.
- Add native host mapping for common filesystem failures into `fs_err`
  variants.
- Keep wasm/playground unsupported filesystem as a structured host error or an
  unresolved request with a clear displayed reason.

Success condition:

- Native `read_text` can throw/report missing/denied/failed without collapsing
  all errors to `nil`.

### Phase 3: Honest Throw

- Add an associated effect row `throws` to `Throw 'e`. The role declaration
  in `std/error.yu` becomes:

  ```text
  pub role Throw 'e:
    type throws
    our e.throw: [throws] never
  ```

- Lower role declarations so that an associated effect row appears in
  `ret_eff` instead of being clamped to the empty row.
- Synthesized `impl Throw E` from `error E:` sets `type throws = [E]`.
- Switch `std::prelude` from the placeholder identity `\e -> e` to the real
  definition `\e -> e.throw`.
- Auto-generate `impl Display E` for every `error E:` declaration so that the
  value retrieved through `wrap` or surfaced in diagnostics is presentable.

Success condition:

- `\e -> e.throw` works as a transparent generic operator. `fail e` carries
  the impl's effect row through to the call site.
- A regression test demonstrates that the role declaration no longer collapses
  the throw effect to empty.

### Phase 4: Error Aggregation

- Add explicit aggregation examples such as `error io_err: fs from fs_err`.
- Decide how explicit casts/wrapping are written and how generated `from`
  entries interact with ordinary user-defined casts.
- Extend `E::wrap` so that it catches the wider error effect together with
  all `from`-linked narrower error effects in one pass.
- Generate `E::up` in the wider error's companion module as a handler that
  lifts narrower errors into `E` and rethrows them as `E`.

Success condition:

- User code can publish a single error type while internally using multiple
  narrower error families.
- `io_err::up: ...` reads as the standard way to absorb narrower errors into
  the wider effect row.

### Phase 5: Result Type

- `result 'ok 'err = ok 'ok | err 'err` is in `std::result` and serves as the
  value form for error effects closed by `E::wrap`.
- Treat `result` as a helper for closing an error effect into a value, not the
  primary error mechanism.

Success condition:

- User code can choose between handling an error effect directly and converting
  it into a value.

### Phase 6: Filesystem API Stabilization

- Decide whether `path` is a real type or `str` alias.
- Add path helpers.
- Add directory listing and metadata.
- Decide stdin/stdout/stderr relationship to console and fs.
- Add examples and docs.

Success condition:

- The filesystem API is stable enough for public examples.

## Non-Goals

- Do not add exceptions before the recoverable/trap boundary is clear.
- Do not use `result` for compiler diagnostics.
- Do not pretend wasm has native filesystem access.
- Do not expose raw OS errors as stable language semantics.
- Do not introduce an anyhow-style open error namespace or runtime
  `Display`-based dispatch over arbitrary errors. All catching is by name; all
  aggregation is explicit through `from` entries and `wrap` / `up`.

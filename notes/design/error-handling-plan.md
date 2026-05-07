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

## Proposed Direction: Typed Error Effects

The leading candidate is a thiserror-like surface encoded with ordinary data
types and ordinary effects:

- each error family has a concrete algebraic data type;
- the same error family has a corresponding effect/act;
- each error constructor is also an effect operation;
- throwing a data value is provided through a `Throw` role or equivalent sugar;
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

Possible desugaring:

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
  our e.throw = case e:
    fs_err::not_found path -> fs_err::not_found path
    fs_err::denied path -> fs_err::denied path
    fs_err::invalid_path text -> fs_err::invalid_path text
```

The exact `Throw` role signature still needs design. The important point is
that operation names mirror constructor names. This makes handlers direct:

```text
catch read_text path:
  fs_err::not_found path, _ -> fallback
  fs_err::denied path, _ -> ...
```

`error` can be a reserved word for this sugar.

Aggregation remains explicit:

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

On top of that, the generated error namespace can provide an aggregation
handler such as `io_err::unite`. That handler catches child error effects and
rethrows the parent error effect. This lets code collect errors as effects by
placing a handler expression, instead of only by writing a fully annotated
return type.

Sketch:

```text
io_err::unite:
  [_; fs_err; parse_err; e] a -> [io_err; e] a
```

This is the "thiserror-like" path: concrete error enums are the public boundary,
but errors are still carried, peeled, and aggregated by effects.

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
write_text: (str, str) -> bool
exists: str -> bool
is_file: str -> bool
is_dir: str -> bool
```

This is intentionally minimal and unstable. It proves host effect plumbing and
basic native CLI behavior. It should not be documented as stable.

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

### Phase 3: Error Aggregation

- Add explicit aggregation examples such as `error io_err: fs from fs_err`.
- Decide how explicit casts/wrapping are written and how generated `from`
  entries interact with ordinary user-defined casts.
- Implement handler-based aggregation such as `io_err::unite` that catches
  narrower error effects and throws the wider API error effect.

Success condition:

- User code can publish a single error type while internally using multiple
  narrower error families.

### Phase 4: Result Type

- Add `result 'ok 'err = ok 'ok | err 'err` only if value-level error capture is
  still useful after error effects exist.
- Treat `result` as a helper for closing an error effect into a value, not the
  primary error mechanism.

Success condition:

- User code can choose between handling an error effect directly and converting
  it into a value.

### Phase 5: Filesystem API Stabilization

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

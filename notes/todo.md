# Yulang Todo

This is a local working note. Keep it short and update it when the project
direction changes.

## Current Direction

Yulang now has the core language shape, a working VM, wasm playground, std
library prototypes, host effects, compiled-unit cache prototypes, and enough
examples to show the intended scripting experience.

The next work should focus on three large tracks:

1. compile to native-quality code;
2. make parsing a first-class Yulang/library capability;
3. stabilize host/filesystem specifications.

## Priority 1: Native Backend

Goal: compile Yulang programs through CPS-style lowering into Cranelift, while
keeping the current VM as the reference implementation and debugging target.

Target shape:

```text
Core / runtime IR
  -> explicit control/effect representation
  -> CPS or CPS-like continuation lowering
  -> closure/environment representation
  -> Cranelift IR
  -> native object / executable / JIT
```

TODO:

- Define the IR boundary that feeds CPS lowering.
- Decide how algebraic effects, resumptions, and `bind_here` map to
  continuations.
- Decide closure and environment layout.
- Decide value representation for ints/floats/bools/unit/strings/lists/records
  and variants.
- Keep VM and Cranelift output comparable with small golden/runtime tests.
- Start with pure functions and first-order calls before effect handlers.
- Add a benchmark path that compares VM vs Cranelift for the same examples.

Non-goals for the first slice:

- Do not remove the VM.
- Do not compile every runtime feature at once.
- Do not optimize before the representation boundary is clear.

## Priority 2: Parser Combinators

Goal: implement parser combinators as a language/library capability, not only as
compiler internals.

Target shape:

```text
source text / stream
  -> parser value
  -> success(value, rest) | structured parse error
```

TODO:

- Decide whether the first parser API is pure, effectful, or both.
- Define parser result and error types.
- Implement the minimal combinator set:
  - `item`
  - `satisfy`
  - `map`
  - `and_then`
  - choice
  - repetition
  - optional
  - token/string matching
- Decide how backtracking, cut/commit, and error merging work.
- Add examples that parse a small expression language and a config-like format.
- Keep the compiler parser separate unless/until the library API is proven.

Non-goals for the first slice:

- Do not rewrite the compiler parser around the new library immediately.
- Do not expose parser internals that would freeze the compiler parser design.

## Priority 3: Host / Filesystem Specification

Goal: make ordinary script host capabilities feel stable and predictable without
making the playground unsafe or pretending every host supports the same things.

Detailed plan:

- `notes/design/error-handling-plan.md`

Current status:

- `std::console` provides `print` / `println`.
- `std::fs` is a first minimal native-host surface:
  - `read_text: str -> opt str`
  - `write_text: (str, str) -> bool`
  - `exists: str -> bool`
  - `is_file: str -> bool`
  - `is_dir: str -> bool`
- The exact filesystem API is intentionally TODO. Current names and return
  shapes are a prototype, not a stable contract.
- Native CLI/basic host handles `std::fs` requests through Rust `std::fs`.
- Wasm/playground leaves filesystem requests unresolved for now.

TODO:

- Design error handling before stabilizing `result` or expanding `std::fs`.
- Decide the stable error model:
  - `opt`
  - `result`
  - exception/effect-style errors
  - structured diagnostics from host requests
- Decide path handling:
  - plain `str`
  - `path` type
  - path join/dirname/basename/extension helpers
- Decide directory operations:
  - `list_dir`
  - recursive walking
  - metadata
- Decide input/output streams:
  - stdin/stdout/stderr
  - binary bytes vs text-only first API
- Decide capability policy:
  - native CLI defaults
  - playground behavior
  - explicit deny/allow list
- Add examples only after the API is no longer obviously provisional.

## Supporting Track: Static Analysis Speed

Goal: keep playground and scripting latency low.

Detailed plan:

- `notes/design/static-analysis-speed-plan.md`
- `notes/design/partial-compilation-cache-plan.md`

TODO:

- Continue moving principal elaboration toward measured one-pass execution.
- Expand compiled-unit typed-surface import for role/impl/effect lookup fidelity.
- Tighten compiled-unit manifest validation.
- Generalize persistent cache from std to user dependency SCCs.
- Keep benchmark scripts and phase timings current.

## Supporting Track: Diagnostics and Docs

Goal: make the language usable without reading implementation notes.

TODO:

- Improve parser/type/runtime diagnostics with source frames.
- Keep examples runnable from CLI and playground.
- Add docs for host effects once filesystem semantics settle.
- Add known limitations that match the current implementation.
- Keep README short and point to playground, examples, and design notes.

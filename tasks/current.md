# Current Task: post-core roadmap

Yulang has enough core language/runtime functionality to move from "can this
language work?" toward "can this become a practical scripting language?".

The current work should be organized around three main tracks.

## Track 1: Native Backend

Build a Cranelift backend through an explicit control representation.

Near-term shape:

```text
runtime/core IR
  -> CPS or CPS-like control IR
  -> closure/environment layout
  -> Cranelift IR
```

Immediate TODO:

- Write a design note for the CPS/Cranelift boundary.
- Pick the first supported subset:
  - pure first-order functions;
  - primitive numeric/string operations;
  - simple records/variants if representation is clear.
- Keep algebraic effects and resumptions in the design, but do not make them
  the first compiled milestone.
- Add a small VM-vs-Cranelift comparison harness before optimizing.

Key constraint:

- The VM remains the behavioral oracle. Native code should be added beside it,
  not as a replacement.

## Track 2: Parser Combinators

Implement parser combinators as a Yulang-facing capability.

Immediate TODO:

- Define the public parser result and error type.
- Implement the minimal combinator kernel:
  - `item`
  - `satisfy`
  - `map`
  - sequencing / bind
  - choice
  - repetition
  - token/string matching
- Decide how cut/commit and error merging should behave.
- Add examples after the first API can parse something nontrivial.

Key constraint:

- Do not rewrite the compiler parser yet. The library parser API should prove
  itself independently first.

## Track 3: Host / Filesystem Semantics

Stabilize host capabilities, especially filesystem behavior.

Design reference:

- `notes/design/error-handling-plan.md`

Current implementation:

- `std::console` has `print` / `println`.
- `std::fs` exists as a provisional native-host surface:
  - `read_text: str -> opt str`
  - `write_text: (str, str) -> bool`
  - `exists: str -> bool`
  - `is_file: str -> bool`
  - `is_dir: str -> bool`
- Native CLI/basic host handles these requests.
- Wasm/playground leaves filesystem requests unresolved.

Immediate TODO:

- Do error handling design before introducing/stabilizing `result`.
- Treat the exact `std::fs` API as unstable.
- Decide error handling before expanding the API:
  - `opt`
  - `result`
  - structured host-request errors
  - effect-style error operations
- Decide whether paths stay as `str` or become a `path` type.
- Decide the first directory API, probably after text read/write settles.
- Decide playground capability policy before making browser examples.

Key constraint:

- Do not accidentally make native-only filesystem behavior look portable to
  wasm/playground.

## Ongoing: Static Analysis Speed

The recent performance work is still aligned with the playground goal.

Current references:

- `notes/design/static-analysis-speed-plan.md`
- `notes/design/partial-compilation-cache-plan.md`

Current checkpoint:

- Principal-unify is the default monomorphize route.
- Specialization body rewrite is now queued and profiled by target.
- Block rewrite avoids a redundant pre-walk and significantly reduces
  `showcase` monomorphize time.
- Compiled-unit artifacts exist for syntax/namespace/typed/runtime surfaces.
- Wasm embeds std compiled-unit artifacts and uses source std as fallback.

Next TODO:

- Expand role/impl/effect fidelity in typed-surface import.
- Tighten compiled-unit manifest validation.
- Generalize persistent cache to user dependency SCCs.
- Keep `bench/static_analysis_bench.sh` representative.

## Ongoing: Diagnostics and Examples

Keep examples as the public contract while the language is experimental.

TODO:

- Keep playground examples runnable from CLI.
- Add examples only when the feature behavior is stable enough to explain.
- Improve user-facing diagnostics for parser/type/runtime errors.
- Avoid exposing internal monomorphize/runtime errors in ordinary user paths.

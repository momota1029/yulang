# Browser playground bootstrap

## User-facing path

Added a Vite page and `yulang-wasm` leaf crate around the existing
`yu_playground::infer` and `yu_playground::execute` entry points. The page can
inspect a candidate inference graph or run a selected definition. It includes
ordinary, conditional, and handled-operation examples and keeps source in the
browser. `tools/inference-playground/README.md` documents how to run and build
it.

This is a WebAssembly front end for the current experimental playground. It
does not provide Yulang2 compatibility, standard-library imports, arithmetic,
or production admission. The 3,316 KB Wasm artifact (969 KB gzip in the Vite
build) also needs size reduction before a hosted demo would feel lightweight.

## Release-only inference failure and repair

The first Wasm execution panicked in
`InferenceSession::component_endpoint`. Reproduction with the native optimized
CLI showed the same failure. Both component collection paths had placed
`component_term_positions.insert(...)` inside `debug_assert!`; optimized builds
remove the entire assertion expression, including the required map insertion.
The insertion now always runs and only the duplicate check remains conditional.

This changes no inference rule. It restores the already intended term-to-recipe
index in optimized builds, allowing the candidate solver and evaluator to run.

## Verification

- `cargo check -p yulang-wasm --target wasm32-unknown-unknown` passed.
- Before the fix, an optimized native CLI invocation panicked at
  `component_endpoint`; this reproduced the Wasm failure.
- `cargo test --release -p yu-playground --test cli_approved_surface ordinary_callable_runs_from_public_stdin_cli -- --exact` passed (1 test).
- `npm run build` passed, including `wasm-pack build` and Vite production build.
- `npm run typecheck` passed.
- `npm run check` rebuilt the page and passed its Node smoke test. The smoke
  calls `infer` on polymorphic identity, `run` on identity application, and
  `run` on a handled operation. Runtime results are `7\n` and `7\n`; inference
  returns the candidate graph header.

The test/build evidence establishes one optimized ordinary CLI case, one
candidate inference call, one ordinary Wasm run, and one closed primitive
effect handler run. It does not establish broad language coverage, visual
browser compatibility, Yulang2 parity, soundness, principality, or evaluator
proof closure. Existing source/evaluator and Simple-sub gates remain OPEN.

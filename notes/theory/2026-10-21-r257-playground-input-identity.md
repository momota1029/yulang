# R257 — Y2 playground input identity locator

Status: primary-only, read-only locator result; no independent review.

The pinned Y2 Types and Console examples in `web/playground/src/main.ts`
flow from `examples[index].source` into the editor value. `runSource` passes
that value to `requestRun`; `run-worker.ts` forwards it as `run(source, lang)`
to the WASM export. The WASM embedded-std path passes the same source string to
Yulang's source-build entry, whether the embedded standard library comes from
source or a compiled artifact.

`crates/yulang/src/source/std_sources.rs` constructs the root `SourceFile` at
`Path::default()` and prepends the implicit prelude/module source before
loading. `crates/sources/src/lib.rs` retains the loaded source and GreenNode;
`crates/parser/src/lib.rs` is the parser entry. The parser dispatches
`our`/`pub` declarations to Binding nodes and a parenthesized expression to a
Paren node with an ordered comma-separated expression list.

This closes the owner-location gap for the Web-to-parser input route. It does
not instantiate the registered sample declaration vector or its DefIds. The
exact parsed declaration-to-registration join, full initializer census,
composed runtime-root order, specialization success and sample-specific
Request reachability remain UNKNOWN. No sample run, tests, builds, code changes
or parent proof closure resulted. Exact owner blobs and the evidence boundary
are recorded in `tasks/agent-loop/sprints/yulang2-playground-input-identity-20261021-r257.md`.

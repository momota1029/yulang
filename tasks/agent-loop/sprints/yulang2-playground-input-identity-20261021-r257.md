# R257 — pin the Y2 playground source-input bridge

Status: primary-only read-only locator result. This does not certify a sample
declaration-to-DefId join, initializer census, runtime order, or Request reachability.
No compiler edits, tests, builds, sample executions, or production admission.

## Goal and boundary

Continue the unchanged R149 Types/Console outcome under
`notes/design/2026-10-20-r149-types-console.md`. Use only the pinned Y2 oracle
commit `a58eefc31e22141574b6f20c6a5748151c6d79f1` and the repository-local
Y3 evidence already frozen by R149/R154/R256. This pass locates how the exact
Web examples reach the Y2 source loader and parser. It does not claim a runtime
trace or add compiler authority.

R149's examples are the exact 142-byte Types source (SHA-256
`8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`) and
92-byte Console source (SHA-256
`ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`). Their
literal templates are pinned in the R149 design and Y2
`web/playground/src/main.ts` blob `e6bec9fe44d673ccbf98af078ef4562c9267ef6c`.

## Located immutable owners

| Y2 owner | Blob | Located relation |
|---|---|---|
| `web/playground/src/main.ts` | `e6bec9fe44d673ccbf98af078ef4562c9267ef6c` | Defines the exact Types and Console examples. `loadExample` assigns `examples[index].source` to the textarea; `runSource` reads that value and passes it to `requestRun`. |
| `web/playground/src/run-worker.ts` | `efa6de1add1f31f405d0086bf17d3801df39df0a` | Receives the run request and calls `run(request.source, request.lang)` after WASM initialization. |
| `crates/wasm/src/lib.rs` | `c7ba26b3f07ea3aa9a7ba785ca3b0210d3eb9f75` | Exposes `run(source, lang)` and routes the unchanged `source` through `run_inner_uncached`. The full embedded-std branch passes `source.to_string()` to the Yulang source-build entry, or to the artifact-backed entry with the same source argument. Branch selection is runtime-dependent and is not claimed here. |
| `crates/yulang/src/source/std_sources.rs` | `e8af0c059373699101d53454ab7231a7c85827db` | `embedded_playground_std_loaded_with_root` passes source to `load_with_embedded_prefix`; that builds a root `SourceFile` with `Path::default()` and `source_with_implicit_std_prelude(source)`. The artifact-backed root builder also sends the supplied source to `load_with_embedded_prefix_prelude_only`. |
| `crates/sources/src/lib.rs` | `38d85d7dbb76bca11917963af52f72b17769e3c8` | R154's reviewed generic loader owner: loaded records retain `module_path`, source, and a CST created by `parse_module_to_green_with_ops` or its measured variant. Reused only for that generic construction relation. |
| `crates/parser/src/lib.rs` | `c1af9d4c794c5c8b3bcde5b39d06ceae11b3ff2f` | `parse_module_to_green_with_ops` produces the GreenNode consumed by the sources loader. |
| `crates/parser/src/stmt/mod.rs` | `148e10b751cf64d97e4f079aaa9e9a3b2e6fa891` | Dispatches `our`/`pub` visibility tokens to declaration parsing. |
| `crates/parser/src/stmt/binding.rs` | `2b3a5db721d316856682b1a0e70e2d3b449845e8` | Builds `Binding` with `BindingHeader` and `BindingBody`; body parsing delegates to expression parsing. |
| `crates/parser/src/expr/core.rs` | `d5bec55af7466ce02cea75eb6423a4c53b2714e9` | An opening parenthesis creates a `Paren` syntax node around the delimited expression list. |
| `crates/parser/src/expr/group.rs` | `6e67c74593215ee7c302e85e09571a1be22ed6f1` | The parenthesized expression list recognizes comma and semicolon separators. It preserves item order in the syntax event stream; it does not itself establish the later semantic tuple constructor. |

These observations establish a source-input route: choosing a pinned example
and running it sends the exact editor string through the worker and WASM run
entry to the source-build path. The root source receives the standard implicit
prelude/module prefix; the sample bytes remain the source suffix. In the
artifact-backed path the standard prefix may be supplied by a compiled
artifact, while the root source is still loaded from the supplied sample.

## Result and remaining bridge

The parser/input owner is no longer unknown at the path level. This narrows the
R154 obstruction to the later join from the root GreenNode and its declaration
nodes into the actual registered sample declarations and DefIds. The generic
R154 ModuleTable relation does not instantiate that join. R152 also left the
binding-name/body/shape helpers and complete constructor coverage unresolved.
Those owners need a sequential pin before content inspection outside their
existing reviewed manifests.

No exact browser invocation was executed. No LoadedFile/CST instance, parsed
declaration vector, DefId, ComputedDef count, composed runtime-root order,
specialization result, or sample-specific Request reachability was observed.
These remain UNKNOWN, not zero. The source route alone does not prove the
compiled-artifact branch selected for either example or prove successful
inference/execution. R149, Simple-sub/evaluator A/B, R70/R71, source/native
generality, soundness, principality, and production remain OPEN.

## Verification and status

Evidence consists of immutable Git blob reads and hash pins from the stated Y2
commit, plus already-reviewed R154 generic loader facts. No tests, builds,
sample execution, code changes, or external scratch data were used. This is a
primary-authored locator result with no independent review; it must not be
promoted to a CLEAN source certificate.

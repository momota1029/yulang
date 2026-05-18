# Yulang Native Backend

Yulang has an experimental native backend under active development. The
interpreter (`yulang run`) is the semantic oracle: native paths are enabled
only for the subset listed here and are validated by comparing their output to
the interpreter.

This page is split into two parts:

- A **user-facing support table** describing what currently runs natively
  from Yulang source, organized by what you can try.
- A **detailed status** section describing the current state of the pure-subset
  backend, the effects backend, and the surrounding cache / package
  layout without keeping every historical regression in this public document.

For overall language status across all stages, see
[docs/status.md](status.md). The current native experimental release handoff is
recorded in [docs/native-experimental-release.md](native-experimental-release.md).
For deeper design notes see
`notes/design/native-backend-plan.md`,
`notes/design/cps-effect-lowering-plan.md`, and
`notes/design/native-cps-mainline-plan.md`. The post-prototype native heap and
value-word plan is recorded in `notes/design/native-gc-runtime-plan.md`. The
direct-style / SSA island optimization direction is recorded in
`notes/design/native-direct-style-islands.md`. The current implementation
direction is to make the effects backend the native mainline while keeping the
pure-subset backend as an effect-free speed-checking path and boxed value helper
source. The handler hygiene evidence used by the interpreter and native effect
dispatch is summarized in
[docs/hidden-effect-evidence.ja.md](hidden-effect-evidence.ja.md).

As of 2026-05-18, `yulang run --native` is ready to be treated as an
experimental release candidate for its documented subset. It is still opt-in and
still reports unsupported native shapes instead of silently falling back to the
interpreter. The passing gate covers recursive tuple-returning
handlers, block-tail loop control, finite/open-range `for` with local `last`,
finite nondeterministic list collection, mutable-reference resumptions, and
native pretty-printing of unit/bool/runtime-shaped roots. It also covers
open-range nondeterministic `.once` and a combined `std::junction` + finite
nondet + method-call root on the CPS repr native path.

## Native Direction

Yulang's full native path is planned around **optimized CPS first, then native
code generation**.

```text
Yulang source
  -> runtime IR
  -> effect-aware CPS IR
  -> CPS optimization
  -> Cranelift codegen
       -> JIT
       -> object / executable
```

The effects backend is not meant to stay as a slow interpreter-shaped runtime.
It is the IR where Yulang's full control features become explicit:
handlers, resumptions, thunk boundaries, local returns, loop control, and
hidden effect hygiene. Once those are explicit, the native backend can optimize
them before producing JIT code or an executable.

The main optimization targets are:

- direct jumps for known continuations instead of indirect continuation calls;
- removal of administrative `force` / `return` / `continue` chains;
- static removal of handler and delimiter frames when effect evidence proves
  they cannot catch anything;
- stack / SSA lowering for non-escaping thunks, closures, and continuations;
- direct-style / SSA island extraction for local CPS continuation subgraphs
  that contain no dynamic effect/control boundary;
- specialization of frequently used higher-order control patterns when the
  call-site type, effect, and handler evidence make them concrete. Standard
  library forms such as loops, folds, nondeterminism helpers, and handler
  wrappers should benefit from this, but the optimizer must not depend on
  specific std module paths or function names;
- lowering optimized CPS continuations to Cranelift blocks and block
  parameters.

There is now an explicit CPS optimization stage between effects ABI lowering
and Cranelift codegen. The first real passes rewrite explicit calls to empty
forwarding continuations, fold empty `Return(param)` continuations into the
caller, fold literal boolean branches, reify direct calls to structural
primitive wrappers back into primitive statements, reify local
partial-application closure calls back into direct calls, reify known
partial-application closures passed through continuation
parameters when their captures can be rebased to target parameters, rewrite
known closure `EffectfulApply` terminators back into effectful direct calls or
pure primitive resumes, remove unused continuation parameters and their
matching continuation-call arguments, inline small pure direct callees
including structural value helpers, inline small single-use one-shot
continuations, rewrite effectful-call terminators to pure callees back into
direct calls plus local continuation
jumps, remove dead pure value statements including total primitive statements
and structural projections, and prune continuations that are no longer
reachable from function entries, handler arms, thunks, closures, or terminator
targets. The simplification pipeline runs to a small bounded
fixpoint so newly exposed administrative calls are cleaned up in the same
optimization entrypoint. The stage also profiles direct-style / SSA island
candidates and exposes
`YULANG_CPS_OPT_TRACE` debug output. JIT and object generation share this
entrypoint so individual CPS simplification passes do not fork by artifact
kind. The first island codegen step is also in place: effectful continuation
functions can absorb pure successor continuations as Cranelift blocks, avoiding
local continuation function calls while keeping effectful return routing at
island exits. Direct calls from those islands to pure callee functions now use
plain Cranelift calls rather than the effectful eval-context protocol.

The pure-subset backend remains useful as an effect-free speed-checking path, a
boxed value helper source, and a debugging path. It is not the plan for
implementing the entire Yulang language. The full-feature path should flow
through CPS optimization and then share the same optimized codegen route for JIT
and object / executable output.

## Public CLI

The normal execution entrypoint is `yulang run`. The interpreter remains the
default today, but native execution is available from the same command:

```bash
yulang run program.yu
yulang run --native program.yu
yulang run --native --native-backend pure program.yu
```

`yulang run --native` uses the effects backend because it is the native path
intended to grow toward full Yulang coverage. `--native-backend pure` forces the
pure-subset backend for speed checks and backend debugging.

`run` executes every root expression but does not print root values by default.
Only program output such as `print` / `println` goes to stdout. Add
`--print-roots` when comparing or inspecting root expression values.

The lower-level `yulang native` subcommand remains available for artifact
generation and forced backend work. The `--kind` option selects what to
produce/run; output paths can be set with `--out`.

| Command                                              | Purpose                                                                 |
| ---------------------------------------------------- | ----------------------------------------------------------------------- |
| `yulang run <path>`                                  | Run the file on the reference interpreter.                              |
| `yulang run --native <path>`                         | Compile and run the file through the native effects backend.            |
| `yulang run --native --native-backend pure <path>`   | Compile and run through the pure-subset backend for speed checks.       |
| `yulang run --print-roots <path>`                    | Execute the program and print root expression values for inspection.    |
| `yulang native <path>` (or `--kind run`)             | Compile and run the file through the native effects backend.            |
| `yulang native --kind run-pure-exe <path>`          | Force the pure-subset backend; useful when comparing the effect-free speed-checking path. |
| `yulang native --kind run-effects-exe <path>`        | Force the effects backend; useful when debugging effect lowering. |
| `yulang native --kind run-exe <path>`                | Build and run a scalar native executable.                               |
| `yulang native --kind object --out <path> <file>`    | Emit a native object file rather than running.                          |
| `yulang native --kind exe --out <path> <file>`       | Emit a scalar native executable rather than running.                    |
| `yulang native --kind pure-exe --out <path> <file>` | Emit a pure-subset-backend native executable.                       |
| `yulang debug compare-i64 <path>`                    | Run the program through the interpreter, native control IR, native ABI, and Cranelift scalar paths; report whether the scalar `i64` results agree. |
| `yulang debug abi-lanes <path>`                      | Print the native ABI value representation classification.               |

Default native artifacts are written under `target/yulang`. `--kind` accepts
`object` / `exe` / `pure-exe` / `run` / `run-exe` / `run-pure-exe` /
`run-effects-exe`. The old `value-exe`, `run-value-exe`, and
`run-cps-repr-exe` names remain accepted as compatibility aliases.

## Optimization Tracing

Use `bench/native_cps_opt_trace.sh` to compare the interpreter, pure-subset
executable, forced effects executable, and default native path on a small suite:

```bash
bench/native_cps_opt_trace.sh --repeat 3
```

The script sets `YULANG_CPS_OPT_TRACE=1` for effects paths and prints the
optimizer profile line next to each run. The profile includes input and optimized
continuation / statement counts, pass counters, direct-style island counts, and
the observable output. The wall-clock timings include compile and link work; use
them to spot large regressions, then add a narrower runtime benchmark if a case
looks suspicious.

You can focus on one path or custom files:

```bash
bench/native_cps_opt_trace.sh --modes effects-exe,native examples/04_sub_return.yu
```

## User-facing support

### What you can try natively today

The pure-subset backend covers ordinary first-order data; the effects backend
covers a small but growing slice of effect-shaped programs. The table below is
at the granularity a Yulang user cares about — for the full
checklist, see *Detailed progress* below.

#### Expressions

| Surface form                                        | Stage                  | Status |
| --------------------------------------------------- | ---------------------- | :----: |
| Scalar literals (`int` / `float` / `bool` / `unit` / `str`) | pure-subset backend          |   ✅   |
| String concatenation and bytes/path primitives      | pure-subset backend / effects |   ✅   |
| List literals, list merge, length, index, raw view  | pure-subset backend          |   ✅   |
| Tuple, record, variant, record field selection      | pure-subset backend          |   ✅   |
| Record spread expressions                           | pure-subset backend          |   ✅   |
| Literal / list / record / variant / tuple pattern matching, including guards, defaults, and list / record spread patterns | pure-subset backend / effects | △ |
| Lambdas / first-class function values (pure)        | effects (prototype)   |   △   |
| Closures with captured state                        | effects (prototype)   |   △   |
| Closure values selected from records, tuples, and lists and then called | effects (prototype) | △ |

#### Effects

| Surface form                                        | Stage                  | Status |
| --------------------------------------------------- | ---------------------- | :----: |
| Small source-defined algebraic effects              | effects               |   ✅   |
| Multi-shot resumption (scalar)                      | effects               |   ✅   |
| Non-scalar values returned through recursive handler / resumption chains | effects | ✅ |
| `std::undet` `.once` over open-range guarded search | effects | ✅ |
| `std::undet` `.once` / `.list` / `.logic` over finite-list choices | effects |   ✅   |
| Mutable reference edit / update through effects     | effects               |   ✅   |
| Indexed mutable reference update (`&xs[i] = value`) | effects               |   ✅   |
| Effectful thunks across function boundaries         | effects (scalar)      |   △   |
| Stored callback values selected from lists          | effects (prototype)   |   △   |
| `std::junction` effectful boolean conditions        | effects               |   ✅   |
| Combined `std::junction` + finite nondet + post-result method call | effects | ✅ |
| Finite-list `for` loops with `last` / `next` control | effects (scalar)      |   ✅   |
| `sub` / `return` through finite-list and open-range `for`, including use of the returned value in later scalar expressions | effects (scalar) | ✅ |
| Open-range `for` with local `last` result value      | effects               |   ✅   |

#### Output

| Surface form                                        | Status |
| --------------------------------------------------- | :----: |
| Scalar (`i64`-shaped) executable result             |   ✅   |
| Value executable result (printed as a Yulang value) |   ✅   |
| Non-scalar CPS executable result                    |   ✅   |

When a program falls outside the native effects subset, `yulang run --native`
or `yulang native` fails with an effects-backend diagnostic. The interpreter
(`yulang run`) keeps the full language behavior.

The web playground currently runs the interpreter only. It does not expose
native backend selection; use `yulang native` locally when checking the native
pipeline.

## Detailed progress

The remainder of this page is an implementation-side status table. It keeps the
current backend boundaries visible, but detailed regression history lives in
`tasks/current.md` and `notes/progress/`.

### Public CLI status

- [x] `yulang run --native` links and runs a native executable through the
      effects backend.
- [x] `yulang native` (default `--kind run`) links and runs a native executable
      through the effects backend.
- [x] The pure-subset backend is opt-in through `--native-backend pure` or
      `--kind run-pure-exe`.
- [x] The backend-selection helper classifies closure-value roots and closure
      values embedded in records with a structured `closure value` reason.
- [x] Closure values embedded in list-construction primitive payloads are also
      classified with the same structured reason.
- [x] The web playground is explicitly marked as interpreter-only; native
      backend selection is a CLI surface for now.
- [x] `yulang native --kind run-pure-exe` exposes the pure-subset backend directly
      for speed checks and debugging.
- [x] `yulang native --kind run-effects-exe` exposes the effects backend directly
      for debugging.
- [x] Default native artifacts are written under `target/yulang`.

### Pure-Subset Backend Status

- [x] Source-to-runtime lowering can feed the pure-subset backend, and native value
      object/executable generation works.
- [x] Generated executables can print boxed runtime values, including scalar
      values, strings, lists, tuples, records, variants, raw views, and basic
      range/splice results.
- [x] Scalar literals and common numeric/boolean/string primitives run through
      runtime helper symbols.
- [x] Local `my` bindings and top-level non-function bindings can be evaluated
      by the pure-subset backend.
- [x] List literals, list merge, length, index, raw view, range index, and
      splice work.
- [x] Tuple, record, record field selection, record spread expressions, and
      variant construction work.
- [x] Effect-free `if` and the current pattern-match subset work through
      branch/jump lowering.
- [x] Literal, tuple, variant, list, record, and record-spread pattern tests are
      covered in the pure-subset backend when their guards stay inside the
      pure-subset expression subset.
- [x] Native-control eval, native ABI eval, and pure-subset Cranelift share an
      interpreter comparison harness for boxed `VmValue` roots.
- [x] Non-escaping closure allocation, closure environment loads, indirect
      closure calls, partial application wrappers, and branch-carried closure
      handles work in the current pure subset.
- [x] Small std higher-order list programs (`map`, `filter`, `fold`) run through
      the pure-subset executable path when they stay inside the supported
      pure subset.
- [ ] General multi-block control flow outside the current branch/jump subset
      is not supported in the pure-subset backend.
- [ ] Closure values can be called after flowing through the pure-subset backend, but
      printable closure roots and closures embedded as ordinary structural
      runtime values still route to the effects backend.
- [x] The first isolated native GC runtime spike pins down a `YValue` word with
      `i63` immediates, non-aliasing bool/unit immediates, heap references,
      native object headers, traceable object payloads, an explicit root stack,
      root frames and temporary-root helper scopes for helper-call temporaries,
      a `YHeap` allocator boundary, allocation helpers for the first heap
      object set, red-black-tree string/list rope nodes,
      forced-allocation stress tracing, allocated-heap stats, live root-trace
      reports, and add/sub/mul/compare helper smoke coverage for `i63` values
      promoted to heap `BigInt`. The spike also has monomorphic native layout
      descriptors, interned layout handles, typed heap blocks backed by raw
      payload buffers, field offsets, and trace bitmaps for typed fields, so
      `i64`/`u64` closure, continuation, and tuple fields can remain unboxed
      after monomorphization. It also interns static paths and atom-style
      symbol strings into compact native symbols for ADT tags and symbol
      payload lanes, then freezes the closed symbol set into a collision-checked
      hash lookup. Native variant layouts store the tag as a `Symbol` field in
      the raw payload and trace only typed payload fields that are `YValue`.
      The `mmtk-runtime` feature wires in the MMTk crate behind a thin config
      boundary, currently defaulting to a single-threaded `NoGC` spike plan.
      A feature-gated Yulang MMTk VM binding skeleton compiles against MMTk,
      including the initial object header, `YValue` slot representation, memory
      slice, object-size callback, and trace-slot scanner. The first
      `MmtkHeap` prototype implements the `YHeap` boundary and allocates object
      headers, trace slots, and the current semantic `YObject` payload through
      MMTk. It also supports compact raw-payload objects and compact
      `NativeHeapBlock` payloads whose field reads use native layout offsets,
      including closure/thunk/resumption/env/frame payloads. The remaining
      migration is to replace more transitional semantic payload users with
      these compact paths. The `YHeap` read API is already split into
      object-header and trace-child projection, so tracing and stats do not need
      full semantic payload access.
      MMTk heap smoke coverage now exercises debug rendering, allocation stats,
      root trace reports, closure/tuple/string reachability, rope nodes,
      temporary helper roots, compact raw/native-block payloads, and MMTk
      trace-slot scanning, including compact control payloads.
      `MmtkNativeRuntimeContext` exposes the first raw `YValue` word helper
      boundary for unit, bool, int arithmetic/compare, scalar string
      conversions, string construction/concat/index/range/splice/length/equality,
      compact bytes/path conversion helpers, and compact
      tuple/record/variant/list construction/access/view, with record
      default/has/without and list range/splice C ABI smoke paths. A parallel
      `yulang_mmtk_cps_*` symbol set is registered
      behind `mmtk-runtime` for a future all-`YValue` CPS lane; it
      intentionally does not replace the existing `yulang_cps_*` scalar/handle
      ABI. The helper context now creates strings, bytes, and paths as compact
      raw/tree payloads, tuple/record/variant values as compact native blocks,
      and list values as chunked red-black trees. A minimal JIT smoke calls the MMTk CPS helper symbols directly
      and passes `YValue` strings, bytes, and tuples through Cranelift; full
      CPS lowering is still on the existing helper lane by default.
      `CpsReprCraneliftOptions::mmtk_yvalue_primitives()` can opt the CPS repr
      Cranelift path into the current runtime primitive family and
      tuple/record/variant structural statements on the MMTk helper lane. In
      that opt-in lane, Yulang `int`, bool, and unit values are tagged
      `YValue` words; float operations still use unboxed `f64` inputs and box
      boolean results back into `YValue`. Fixed-width `i64`/`u64` layout lanes
      exist in the native layout spike, but they are not source-level Yulang
      types yet. The default CPS path remains on the prototype helper boundary.
- [ ] Generic runtime value layout in the default native path is still backed
      by prototype `VmValue` helpers. The adopted next layout is the isolated
      `YValue` object model above, eventually backed by MMTk.

### Effects Backend Status

- [x] Pure scalar CPS programs, primitive calls, direct calls, conditionals,
      `case` guards, and `sub` / `return`-style control can compile and run
      through the Cranelift effects path.
- [x] Effects ABI modules pass through a shared optimization entrypoint before
      both JIT and object Cranelift codegen. It currently rewrites explicit
      calls to empty forwarding continuations, folds empty return continuations,
      folds literal boolean branches, reifies direct calls to structural
      primitive wrappers, reifies local partial-application closure calls back
      into direct calls, reifies known
      partial-application closures passed through continuation parameters when
      their captures can be rebased to target parameters, rewrites known
      closure `EffectfulApply` terminators back into effectful direct calls or
      pure primitive resumes, removes unused continuation parameters and their
      matching continuation-call arguments, inlines small pure direct callees including
      structural value helpers, inlines
      small single-use one-shot continuations, rewrites effectful calls to pure
      callees into direct calls plus local continuation jumps, removes dead pure
      value statements including total primitive statements and structural
      projections, prunes unreachable continuations, and records
      direct-style / SSA island candidate counts so later thunk/handler passes
      do not fork between artifact kinds.
- [x] The first direct-style island codegen step lowers pure successor
      continuations inside effectful continuation functions as Cranelift blocks
      instead of local continuation calls.
- [x] Direct calls to pure callee functions use a plain call path even when the
      caller is an effectful CPS continuation function.
- [x] Small source-defined algebraic effects and multi-shot resumptions work in
      the CPS evaluator and in the scalar Cranelift prototype.
- [x] Handler entry continuations receive captured environments, and handler
      arms are selected through a dynamic handler stack that crosses function
      boundaries.
- [x] Handler-frame guard snapshots, `LocalPushId` / `PeekId` / `FindId`, and
      `AddId` blocked-effect boundaries are represented in CPS and honored by
      handler selection.
- [x] Inactive `AddId` boundary markers peel older blockers during native
      dispatch, so handler arms can temporarily re-expose local mutable-ref
      effects without leaking unrelated callback effects.
- [x] Thunks and resumptions carry handler-stack and guard-stack snapshots in
      the scalar prototype.
- [x] Thunk boundary masks stay attached to thunk pointers through direct force,
      list index, record field selection, and variant payload projection, so
      hidden callback effects still skip blocked inner handlers.
- [x] `ResumeWithHandler` can rebase captured return frames under a freshly
      installed handler, and the Cranelift path keeps resume-site sibling
      handler environments visible when restored return-frame snapshots resume
      mutable refs.
- [x] Prototype heap handles cover strings, tuples, lists, records, variants,
      closure pointers, thunk pointers, and resumption pointers in the effects
      path.
- [x] String/list/bytes/path/range primitives, conversions, and small host console effects
      are handled through shared runtime helpers or effects helper symbols.
- [x] First-class lambdas, captured closures, partial applications, and closures
      selected from records/lists can be created and called through the effects
      executable path.
- [x] Captured closures stored in tuple values can be recovered through tuple
      patterns and called through the effects executable path.
- [x] Callback values can be stored in lists, recovered with `std::list::index_raw`,
      and called without losing local handler hygiene on the forced effects path.
- [x] Type-converted thunk values can be stored in lists, indexed back out,
      forced with `BindHere`, and run through CPS lowering and Cranelift.
- [x] Lazy operator results in tuple/list value positions are covered by the
      forced effects executable path without leaking visible thunk handles.
- [x] Lazy operator results in record fields and variant payloads are covered by
      the same forced effects executable path.
- [x] Record spread expressions are covered by the effects executable path.
- [x] Effects lowering covers tuple, list, list-spread, record,
      record-spread, record-default, guarded, and variant payload pattern tests
      in `case` arms for the source-shaped regression path.
- [x] Top-level destructuring `my` bindings that lower to self-shadowing
      structural `case` bindings, including record-spread rest bindings, run
      through the default native CLI by routing to effects with a structured
      `structural pattern binding` reason.
- [x] `std::junction`, finite-list `for` loops with `last` / `next`, mutable
      reference update, and finite-list `std::undet` `.once` / `.list` /
      `.logic` choices run through the effects executable path for covered
      observable roots.
- [x] Open-range `std::undet` `.once` and the combined `std::junction` +
      finite `std::undet.each` + post-result record method-call root match the
      VM on the native effects path for the covered release-gate cases.
- [x] `sub` / `return` can escape through finite-list and open-range `for`
      chains on the effects executable path for the covered return-shaped
      roots. Already-escaped handler arms also keep their result when the
      returned value flows into a later scalar expression such as `1 + r`.
- [x] Open-range `for` with local `last` consumes the loop-control arm at the
      loop boundary and continues with the following expression on the effects
      executable path.
- [x] Callback return hygiene is covered by source regressions: direct `f()`
      inside an inner `sub` is captured there, while callback `h()` escapes to
      the caller's `sub`.
- [x] Non-scalar CPS return values that use prototype heap handles print as
      Yulang-like values in generated CPS executables, including the covered
      recursive handler/resumption tuple result.
- [x] Native effects root pretty-print goes through the Debug projection for
      runtime-shaped roots; strings, variants, records, tuples, lists, boxed
      floats, literal bools, and literal units keep their visible value shape.
- [x] Non-scalar values returned through recursive handler/resumption chains
      now keep the forced result and nested handler env, covering
      `examples/10_effect_handler.yu`.
- [ ] General returned/stored effectful thunks still need more source-shaped
      coverage outside the current scalar/prototype subset.
- [x] Forced pure-subset execution rejects the top-level destructuring
      shape as unsupported instead of generating a crashing executable; the
      default native CLI routes it to effects.
- [ ] General closures and heap value lanes in the default effects backend are
      still prototype representations, not finalized native runtime layout.
      The isolated `gc_runtime` module covers closure/thunk/resumption/env
      object allocation, headers, and tracing, but codegen has not been ported
      to it yet.
- [ ] The effects backend is the effectful native mainline, but it is not yet a
      complete replacement for the interpreter.

### Cache and package/build status

- [x] `yulang-compile` owns source-level glue above inference and native
      codegen; `yulang-native` no longer depends on `yulang-infer` directly or
      indirectly.
- [x] `target/yulang` is used for local native experiment outputs.
- [x] Persistent cache paths exist for compiled unit artifacts.
- [x] Realm/band source identity is documented as the direction for package-like
      source boundaries.
- [ ] Compiled unit artifact cache is not yet wired into the main lowering
      pipeline.
- [ ] `realm.toml` / `yulang.lock` are planned but not complete as a full
      package/build workflow.
- [ ] Native executable layout and install/build commands are still prototypes.

## Day-to-day progress

This page intentionally describes shipped behavior. In-flight work,
ignored regressions, and design questions live in:

- `tasks/current.md` — the current focused track.
- `notes/progress/` — daily progress notes.
- `notes/design/native-backend-plan.md` — the longer plan.
- `notes/design/cps-effect-lowering-plan.md` — CPS/effect lowering plan.

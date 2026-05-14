# Yulang Native Backend

Yulang has a native backend under active development. The interpreter
(`yulang run`) is the semantic oracle: native paths are enabled only for
the subset listed here and are validated by comparing their output to the VM.

This page is split into two parts:

- A **user-facing support table** describing what currently runs natively
  from Yulang source, organized by what you can try.
- A **detailed progress log** describing the current state of the value
  backend, the CPS representation backend, and the surrounding cache /
  package layout.

For overall language status across all stages, see
[docs/status.md](status.md). For deeper design notes see
`notes/design/native-backend-plan.md`,
`notes/design/cps-effect-lowering-plan.md`, and
`notes/design/native-cps-mainline-plan.md`. The current implementation
direction is to make the CPS representation backend the native mainline for
effectful programs while keeping the value backend as an effect-free fast path
and boxed `VmValue` helper source. The handler hygiene evidence used by VM and
native effect dispatch is summarized in
[docs/hidden-effect-evidence.ja.md](hidden-effect-evidence.ja.md).

## Public CLI

The native backend is exposed under the `yulang native` subcommand. The
`--kind` option selects what to produce/run; output paths can be set with
`--out`.

| Command                                              | Purpose                                                                 |
| ---------------------------------------------------- | ----------------------------------------------------------------------- |
| `yulang native <path>` (or `--kind run`)             | Compile and run the file natively. Uses the value backend for effect-free fast-path roots and selects the CPS representation backend when effect / handler / thunk-boundary control is present. |
| `yulang native --kind run-value-exe <path>`          | Force the value backend; useful when debugging value-backend coverage.  |
| `yulang native --kind run-cps-repr-exe <path>`       | Force the CPS representation backend; useful when debugging CPS lowering. |
| `yulang native --kind run-exe <path>`                | Build and run a scalar native executable.                               |
| `yulang native --kind object --out <path> <file>`    | Emit a native object file rather than running.                          |
| `yulang native --kind exe --out <path> <file>`       | Emit a scalar native executable rather than running.                    |
| `yulang native --kind value-exe --out <path> <file>` | Emit a value-backend native executable.                                 |
| `yulang debug compare-i64 <path>`                    | Run the program through VM, native control IR, native ABI, and Cranelift scalar paths; report whether the scalar `i64` results agree. |
| `yulang debug abi-lanes <path>`                      | Print the native ABI value representation classification.               |

Default native artifacts are written under `target/yulang`. `--kind` accepts
`object` / `exe` / `value-exe` / `run` / `run-exe` / `run-value-exe` /
`run-cps-repr-exe`.

## User-facing support

### What you can try natively today

The value backend covers ordinary first-order data; the CPS representation
backend covers a small but growing slice of effect-shaped programs. The
table below is at the granularity a Yulang user cares about — for the full
checklist, see *Detailed progress* below.

#### Expressions

| Surface form                                        | Stage                  | Status |
| --------------------------------------------------- | ---------------------- | :----: |
| Scalar literals (`int` / `float` / `bool` / `unit` / `str`) | value backend          |   ✅   |
| String concatenation                                | value backend          |   ✅   |
| List literals, list merge, length, index, raw view  | value backend          |   ✅   |
| Tuple, record, variant, record field selection      | value backend          |   ✅   |
| Record spread expressions                           | value backend          |   ✅   |
| Literal / list / record / variant / tuple pattern matching | value backend    |   △    |
| Lambdas / first-class function values (pure)        | CPS repr (prototype)   |   △   |
| Closures with captured state                        | CPS repr (prototype)   |   △   |

#### Effects

| Surface form                                        | Stage                  | Status |
| --------------------------------------------------- | ---------------------- | :----: |
| Small source-defined algebraic effects              | CPS repr               |   ✅   |
| Multi-shot resumption (scalar)                      | CPS repr               |   ✅   |
| `std::undet` `.once` / `.list` / `.logic` over finite-list choices | CPS repr |   ✅   |
| Mutable reference edit / update through effects     | CPS repr (scalar)      |   ✅   |
| Effectful thunks across function boundaries         | CPS repr (scalar)      |   △   |
| `std::junction` effectful boolean conditions        | CPS repr               |   ✅   |
| Finite-list `for` loops with `last` / `next` control | CPS repr (scalar)      |   ✅   |

#### Output

| Surface form                                        | Status |
| --------------------------------------------------- | :----: |
| Scalar (`i64`-shaped) executable result             |   ✅   |
| Value executable result (printed as a Yulang value) |   ✅   |
| Non-scalar CPS executable result                    |   ✅   |

When a program falls outside this subset, `yulang native` prints
`native-run: value backend unsupported, using CPS repr: ...` and either
succeeds through the CPS representation backend or fails with a
diagnostic. The interpreter (`yulang run`) keeps the full language behavior.

## Detailed progress

The remainder of this page is the implementation-side checklist that
previously lived in the README. It is intentionally fine-grained; new
items move from the user-facing table above into here as they ship,
or out of here into the user-facing table once they stabilize.

### Public CLI status

- [x] `yulang native` (default `--kind run`) links and runs a native executable.
- [x] `yulang native` prefers the value backend for ordinary values.
- [x] `yulang native` falls back to the CPS representation backend only for
      explicit "unsupported by value backend" cases.
- [x] `yulang native --kind run-value-exe` exposes the value backend directly for debugging.
- [x] `yulang native --kind run-cps-repr-exe` exposes the CPS representation backend
      directly for debugging.
- [x] Default native artifacts are written under `target/yulang`.

### Value backend status

- [x] Source-to-runtime lowering can feed the value backend.
- [x] Native value object generation works.
- [x] Generated executables can print native value results, including boxed
      scalar values, raw list views, record spread expressions, and basic
      list/string range and splice results.
- [x] `int`, `float`, `bool`, `unit`, and `str` literals are represented as
      opaque runtime values.
- [x] Basic numeric and boolean primitives run through runtime helper symbols:
      `+`, `-`, `*`, `/`, comparisons, equality, and `not`.
- [x] Basic conversion/string primitives are wired through helpers:
      integer/float/bool to string, string equality, string length, and
      string index/range/splice.
- [x] Local `my` bindings and top-level non-function bindings can be evaluated
      by the value backend.
- [x] String concatenation works.
- [x] List literals, list merge, list length, list index, raw view, range
      index, and splice work.
- [x] Native-control eval, native ABI eval, and value-backend Cranelift share
      a VM comparison harness for boxed `VmValue` roots. This covers
      non-scalar regressions such as string/list range and splice primitives,
      record selection, record spread expressions, and list spread pattern
      bindings.
- [x] String range index and splice work.
- [x] Tuple, record, record field selection, record spread expressions, and
      variant construction work.
- [x] Value-backend branch/jump lowering works for effect-free `if` and the
      current pattern-match subset.
- [x] Variant tag tests, variant payload binding, and tuple payload binding
      work in value-backend pattern matching.
- [x] Literal pattern tests work in value-backend pattern matching through
      boxed runtime value equality.
- [x] List pattern length tests, prefix/spread/suffix bindings, and refutable
      list item tests work in the value backend.
- [x] Record pattern field tests and bindings work in the value backend,
      including shorthand fields such as `{ok, n}`.
- [x] Record-spread patterns bind the remaining record fields in the VM,
      native-control eval, ABI eval, and value backend.
- [x] Guarded pattern matching works when the guard expression stays inside
      the existing value-backend expression subset.
- [ ] General multi-block control flow outside the current branch/jump subset
      is not supported in the value backend.
- [x] Non-escaping closure allocation, closure environment loads, and indirect
      closure calls work in the value backend when the closure is allocated and
      called inside the compiled subset.
- [x] Closure values are represented as opaque runtime handles in the value
      backend, so indirect closure calls can cross branch/jump block params.
- [x] Value-backend representation analysis propagates closure handles through
      branch/jump block params and rejects closure roots or closure handles
      embedded in tuple/list/record/variant `VmValue` helpers before codegen.
- [x] Source-level value-backend executable tests cover a branch-selected
      captured closure flowing through a zero-arity binding and then being
      applied indirectly.
- [x] Top-level function partial application lowers to generated closure
      wrappers in the value backend and is covered by a source-level executable
      test.
- [x] Value-backend codegen and ABI validation carry values defined in
      dominating predecessor blocks, so std `list.map`, `list.filter`, and
      `list.fold` source programs now run through the value executable path.
- [ ] Closure values can be called after flowing through the value backend, but
      they are not yet printable roots or ordinary structural runtime values
      inside tuples/lists/records.
- [ ] Generic runtime value layout is still backed by `VmValue`; compact native
      representations are not finalized.

### CPS representation backend status

- [x] Pure scalar CPS programs can be compiled with Cranelift.
- [x] Small source-defined algebraic effects can be lowered through CPS.
- [x] Multi-shot resumption prototypes work for scalar programs.
- [x] Simple handler arms, value arms, primitive calls, direct calls, and
      conditional control are covered by regression tests.
- [x] `case` guards with scalar pattern bindings and pure scalar comparisons
      lower through the CPS repr Cranelift path.
- [x] `sub`/`return`-style control has a small CPS repr regression path.
- [x] Tuple, record, variant, and record selection can be lowered and evaluated
      in the CPS/CPS-repr interpreters.
- [x] CPS repr Cranelift can build small records as prototype heap values and
      select fields from them.
- [x] CPS/CPS-repr interpreters reuse the native-control primitive evaluator
      for ordinary `VmValue` primitives, so string/list range, splice, view,
      equality, and conversion semantics stay aligned with the value backend.
- [x] Handler entry continuations receive captured environments in the
      Cranelift CPS repr path.
- [x] Lazy branch conditions that flow through thunk-valued continuation params
      are forced before the Cranelift branch condition is tested.
- [x] CPS repr Cranelift has a small thunk trampoline helper for `ThunkPtr`
      values used by lazy conditions and root wrappers.
- [x] CPS/CPS-repr interpreters can rebase a captured continuation under a
      freshly installed handler.
- [x] CPS repr evaluator carries handler-frame guard snapshots and skips a
      blocked handler frame when resolving `Perform`.
- [x] `LocalPushId`, `PeekId`, and `FindId` have native CPS guard statements in
      the CPS/CPS-repr interpreter paths.
- [x] CPS repr Cranelift has scalar guard-stack helper symbols for
      `FreshGuard`, `PeekGuard`, and `FindGuard`.
- [x] CPS repr Cranelift resumptions and thunks carry handler-stack and
      guard-stack snapshots in the scalar prototype.
- [x] CPS repr Cranelift thunks snapshot handler arm environments for handler
      frames whose captures are available at thunk creation time.
- [x] CPS repr Cranelift can rebase a resumption with `ResumeWithHandler` and
      skip a blocked handler frame for scalar handler tests.
- [x] CPS repr Cranelift can select handler arms across function boundaries
      through globally numbered handler ids and the dynamic handler stack.
- [x] CPS lowering carries `AddId` blocked guards into `Perform` in the
      CPS/CPS-repr interpreter paths.
- [x] CPS lowering resolves `AddId(Var(id))` through the enclosing
      `LocalPushId` guard scope, including handler-body lowering paths used by
      callback hygiene boundaries.
- [x] CPS repr Cranelift can lower `IntToString` to a prototype string handle,
      so small `.show`-style scalar string conversions can pass through the
      CPS repr executable path.
- [x] CPS repr Cranelift can lower `IntToHex`, `IntToUpperHex`, and
      `BoolToString` to the same prototype string handle.
- [x] CPS repr Cranelift can lower native `f64` float literals, arithmetic,
      comparisons, plain-value `ForceThunk`, and `FloatToString` for scalar
      and small effectful-console paths.
- [x] CPS repr Cranelift can lower string literals and a small raw string
      primitive set (`concat`, equality, length, index, raw range, raw splice)
      to the same prototype string handle.
- [x] CPS repr Cranelift can normalize `range` values for list/string range
      index and splice primitives, including source forms such as
      `("aあ🙂z").index (1..<3)`.
- [x] CPS repr Cranelift handles unhandled host `console.print` / `println`
      operations by printing the payload and resuming with unit. This covers
      callback-return hygiene examples that print an intermediate value before
      returning a scalar root.
- [x] CPS/CPS-repr interpreters keep `AddId` effect boundaries on thunk
      values, activate boundary guards during thunk force, and use those
      guards while resolving `Perform`.
- [x] CPS repr Cranelift stores active thunk-boundary guard masks on thunk
      pointers, activates them while forcing thunks, and combines them with
      static `Perform.blocked` guards during handler selection.
- [x] Mutable reference edit/update runs through effect-aware CPS and the
      Cranelift CPS repr scalar path with VM comparison.
- [x] A minimal `once`-style branch handler can resume the first branch from
      tail and boolean-match condition effect operations in the Cranelift CPS
      repr scalar path.
- [x] A DFS `once` kernel with local `choice::branch` / `choice::reject` can
      try `k true`, handle rejection, resume `k false`, and match the VM in the
      Cranelift CPS repr scalar path.
- [x] A finite-list nondeterministic choice can use `std::list::uncons` without
      `fold` / `sub` and return a scalar through the Cranelift CPS repr path.
- [x] `std::undet` `.once` over a finite list compiles and runs through the
      CPS repr object/executable path for scalar roots.
- [x] `std::undet` `.once` can return `opt::just v` through the Cranelift CPS
      repr scalar path and an outer `case` can unwrap the scalar payload.
- [x] `std::undet` `.once` can skip an initially rejected finite-list choice
      and agree with the VM for the first accepted scalar result.
- [x] `std::undet` `.once` handles all-rejected finite lists and nested
      finite-list choices through the Cranelift CPS repr scalar path.
- [x] `std::junction::junction { true }`, explicit `case junction { ... }`,
      and `if all [1, 2, 3] < any [2, 3, 4]` run through the Cranelift CPS
      repr scalar path.
- [x] Finite-list `for` loops, including `last` / `next` loop control, run
      through the Cranelift CPS repr scalar path for scalar observable roots.
- [x] First-class lambda values can be created and applied through the
      Cranelift CPS repr scalar path for pure higher-order calls.
- [x] Effect-flow closure / continuation environments are no longer limited to
      four slots in the CPS repr Cranelift path; larger environments are copied
      through `*_many(ptr, len)` runtime helpers.
- [x] CPS repr Cranelift thunk environments are no longer limited to four
      slots; larger thunk captures are copied through
      `yulang_cps_make_thunk_i64_many(ptr, len)`.
- [x] CPS repr ABI has a dedicated `ClosurePtr` lane, keeping closure pointers
      distinct from `RuntimeValuePtr`, `ThunkPtr`, and resumption pointers.
- [x] Top-level function partial application lowers to CPS closure creation in
      the CPS repr path and is covered by VM / CPS / Cranelift comparison.
- [x] Small std higher-order list programs (`map`, `filter`, `fold`) run through
      the forced CPS repr executable path.
- [ ] General thunk values are only partially represented; thunk roots can be
      forced only while they stay in the scalar CPS repr subset.
- [x] Effectful thunks returned across an inlinable source-defined function
      boundary now carry the caller's active handler frame: a non-recursive
      helper such as `each_head(xs): [choice] int` is inlined and the implicit
      thunk is forced inside the caller's handler scope.
- [x] Handler arms that already continue to their installed escape
      continuation are no longer wrapped as a second scope return in the CPS,
      CPS repr, or Cranelift paths. This keeps `sub` results embedded in
      structural values such as lists from applying the post-catch continuation
      twice.
- [x] Recursive helpers such as `each_list(xs): [choice] int` route effects
      to the caller's handler through the runtime handler stack. CPS lowering
      emits `InstallHandler` / `UninstallHandler` around handler scopes; the
      CPS evaluators thread `active_handlers` through `DirectCall` /
      `ApplyClosure` / `ForceThunk`; Cranelift backs the new stmts with
      thread-local install/uninstall helpers that share the existing
      handler-stack runtime.
- [x] Single-argument top-level function values can be passed through a
      higher-order helper and return an effectful thunk through the Cranelift
      CPS repr scalar path.
- [x] `std::undet.each` runs through CPS eval, CPS repr eval, and the
      Cranelift JIT against a local DFS once helper. Handler-arm
      non-local returns propagate through every internal call site as
      `CpsRuntimeValue::Aborted` in the evaluators and as a scoped
      thread-local abort signal in the Cranelift runtime, so a
      `sub::return` inside a `fold` callback skips the surrounding
      `reject()` and reaches the handler scope.
- [x] Recursive handler wrappers are not direct-call inlined in CPS lowering,
      so simple all-solution nondeterminism such as `branch().list` can lower
      and run through the CPS repr executable path instead of recursively
      expanding the wrapper at compile time.
- [x] Full DFS `std::undet.list` over `each [1, 2, 3]` runs through the
      CPS repr executable path. Returned thunks are forced before consuming
      the immediate-force return frame, so the false branch resumes through
      the enclosing fold and reaches the trailing `reject()` instead of
      leaking `()` into `.list`.
- [x] Nested finite-list nondeterminism such as
      `(each [1, 2, 3] + each [10, 20]).list` runs through CPS eval,
      CPS repr eval, and the Cranelift CPS repr executable path.
- [x] `std::undet.logic` over nested finite-list choices runs through CPS eval,
      CPS repr eval, and the Cranelift CPS repr executable path. The CPS repr
      evaluator and Cranelift helper now treat resumption pointers as
      closure-like callable values for `ApplyClosure`, which keeps queued
      multi-shot continuations usable after `std::list::uncons`.
- [x] `std::undet.once` over nested finite-list choices returns the first
      solution through CPS eval, CPS repr eval, and the Cranelift CPS repr
      executable path.
- [x] `ResumeWithHandler` restores captured return frames in the Cranelift CPS
      repr path, so direct-call caller-rest continuations can run under the
      temporary handler installed around `k true`.
- [x] Closure-application caller-rest through `EffectfulApply` can route an
      effectful operation through a callback and still run the caller's
      post-call continuation under the temporary `ResumeWithHandler` handler.
- [x] Source-level callback return hygiene is covered in the CPS repr scalar
      path: direct `f()` inside an inner `sub` is captured there, while
      callback `h()` escapes to the caller's `sub`.
- [x] The same callback hygiene split is covered by executable-path source
      regressions with observable roots: direct `f()` leaves the outer root at
      `2`, while callback `h()` returns from the outer `sub` as `0`.
- [x] String, list, record, and variant payloads can cross a small source-shaped
      handler / resumption boundary in the CPS repr Cranelift path and print as
      Yulang-like values.
- [ ] General closures and heap value lanes are not complete.
- [x] Non-scalar CPS return values that use the prototype tuple / list /
      record / variant / string heap handles print as Yulang-like values in
      generated CPS executables.
- [ ] This path is still a prototype, not the default full-language runtime.

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

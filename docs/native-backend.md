# Yulang Native Backend

Yulang has a native backend under active development. The interpreter
(`--run`) is the semantic oracle: native paths are enabled only for the
subset listed here and are validated by comparing their output to the VM.

This page is split into two parts:

- A **user-facing support table** describing what currently runs natively
  from Yulang source, organized by what you can try.
- A **detailed progress log** describing the current state of the value
  backend, the CPS representation backend, and the surrounding cache /
  package layout.

For overall language status across all stages, see
[docs/status.md](status.md). For deeper design notes see
`notes/design/native-backend-plan.md` and
`notes/design/cps-effect-lowering-plan.md`. The handler hygiene evidence
used by VM and native effect dispatch is summarized in
[docs/hidden-effect-evidence.ja.md](hidden-effect-evidence.ja.md).

## Public CLI

| Command                          | Purpose                                                                 |
| -------------------------------- | ----------------------------------------------------------------------- |
| `--native-run <path>`            | Compile and run the file natively. Prefers the value backend, falls back to the CPS representation backend for explicitly unsupported cases. |
| `--native-run-value-exe <path>`  | Force the value backend; useful when debugging value-backend coverage.  |
| `--native-run-cps-repr-exe <path>` | Force the CPS representation backend; useful when debugging CPS lowering. |
| `--native-compare-i64 <path>`    | Run the program through VM, native control IR, native ABI, and Cranelift scalar paths; report whether the scalar `i64` results agree. |
| `--native-abi-lanes <path>`      | Print the native ABI value representation classification.               |
| `--native-object <path>`         | Emit a native object file rather than running.                          |
| `--native-exe <path>` / `--native-executable <path>` | Emit a native executable rather than running.       |

Default native artifacts are written under `target/yulang`.

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
| `std::undet` `.once` first solution over a finite list | CPS repr            |   ✅   |
| Mutable reference edit / update through effects     | CPS repr (scalar)      |   ✅   |
| Effectful thunks across function boundaries         | CPS repr (scalar)      |   △   |
| `std::junction` effectful boolean conditions        | CPS repr               |   ✅   |
| Finite-list `for` loops with `last` / `next` control | CPS repr (scalar)      |   ✅   |

#### Output

| Surface form                                        | Status |
| --------------------------------------------------- | :----: |
| Scalar (`i64`-shaped) executable result             |   ✅   |
| Value executable result (printed as a Yulang value) |   ✅   |
| Non-scalar CPS executable result                    |   ❌   |

When a program falls outside this subset, `--native-run` prints
`native-run: value backend unsupported, using CPS repr: ...` and either
succeeds through the CPS representation backend or fails with a
diagnostic. The interpreter (`--run`) keeps the full language behavior.

## Detailed progress

The remainder of this page is the implementation-side checklist that
previously lived in the README. It is intentionally fine-grained; new
items move from the user-facing table above into here as they ship,
or out of here into the user-facing table once they stabilize.

### Public CLI status

- [x] `--native-run` links and runs a native executable.
- [x] `--native-run` prefers the value backend for ordinary values.
- [x] `--native-run` falls back to the CPS representation backend only for
      explicit "unsupported by value backend" cases.
- [x] `--native-run-value-exe` exposes the value backend directly for debugging.
- [x] `--native-run-cps-repr-exe` exposes the CPS representation backend
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
- [x] Guarded pattern matching works when the guard expression stays inside
      the existing value-backend expression subset.
- [ ] Record-spread patterns are not supported in the value backend.
- [ ] General multi-block control flow outside the current branch/jump subset
      is not supported in the value backend.
- [ ] Closure allocation, closure environments, and indirect closure calls are
      not supported in the value backend.
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
- [ ] General thunk values are only partially represented; thunk roots can be
      forced only while they stay in the scalar CPS repr subset.
- [x] Effectful thunks returned across an inlinable source-defined function
      boundary now carry the caller's active handler frame: a non-recursive
      helper such as `each_head(xs): [choice] int` is inlined and the implicit
      thunk is forced inside the caller's handler scope.
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
- [x] `ResumeWithHandler` restores captured return frames in the Cranelift CPS
      repr path, so direct-call caller-rest continuations can run under the
      temporary handler installed around `k true`.
- [x] Closure-application caller-rest through `EffectfulApply` can route an
      effectful operation through a callback and still run the caller's
      post-call continuation under the temporary `ResumeWithHandler` handler.
- [ ] General closures and heap value lanes are not complete.
- [ ] Non-scalar CPS return values can flow through the prototype as opaque
      `i64` heap pointers, but generated CPS executables do not yet print them
      as Yulang values.
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

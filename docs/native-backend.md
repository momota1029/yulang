# Yulang Native Backend

Yulang has a native backend under active development. The interpreter
(`yulang run`) is the semantic oracle: native paths are enabled only for
the subset listed here and are validated by comparing their output to the VM.

This page is split into two parts:

- A **user-facing support table** describing what currently runs natively
  from Yulang source, organized by what you can try.
- A **detailed status** section describing the current state of the value
  backend, the CPS representation backend, and the surrounding cache / package
  layout without keeping every historical regression in this public document.

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
| Literal / list / record / variant / tuple pattern matching, including guards, defaults, and list / record spread patterns | value backend / CPS repr | △ |
| Lambdas / first-class function values (pure)        | CPS repr (prototype)   |   △   |
| Closures with captured state                        | CPS repr (prototype)   |   △   |
| Closure values selected from records and then called | CPS repr (prototype)  |   △   |

#### Effects

| Surface form                                        | Stage                  | Status |
| --------------------------------------------------- | ---------------------- | :----: |
| Small source-defined algebraic effects              | CPS repr               |   ✅   |
| Multi-shot resumption (scalar)                      | CPS repr               |   ✅   |
| Non-scalar values returned through recursive handler / resumption chains | CPS repr | △ |
| `std::undet` `.once` / `.list` / `.logic` over finite-list choices | CPS repr |   ✅   |
| Mutable reference edit / update through effects     | CPS repr (scalar)      |   ✅   |
| Effectful thunks across function boundaries         | CPS repr (scalar)      |   △   |
| Stored callback values selected from lists          | CPS repr (prototype)   |   △   |
| `std::junction` effectful boolean conditions        | CPS repr               |   ✅   |
| Finite-list `for` loops with `last` / `next` control | CPS repr (scalar)      |   ✅   |
| `sub` / `return` through finite-list and open-range `for` | CPS repr (scalar) | ✅ |
| Open-range `for` with local `last` result value      | CPS repr               |   △   |

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

The web playground currently runs the VM interpreter only. It does not expose
native backend selection; use `yulang native` locally when checking the native
pipeline.

## Detailed progress

The remainder of this page is an implementation-side status table. It keeps the
current backend boundaries visible, but detailed regression history lives in
`tasks/current.md` and `notes/progress/`.

### Public CLI status

- [x] `yulang native` (default `--kind run`) links and runs a native executable.
- [x] `yulang native` prefers the value backend for ordinary values.
- [x] `yulang native` falls back to the CPS representation backend only for
      explicit "unsupported by value backend" cases.
- [x] Closure-value roots and closure values embedded in records are selected
      for the CPS representation backend with a structured `closure value`
      reason before the value backend is tried.
- [x] Closure values embedded in list-construction primitive payloads are also
      selected for the CPS representation backend with the same structured
      reason.
- [x] The web playground is explicitly marked as VM-interpreter-only; native
      backend selection is a CLI surface for now.
- [x] `yulang native --kind run-value-exe` exposes the value backend directly for debugging.
- [x] `yulang native --kind run-cps-repr-exe` exposes the CPS representation backend
      directly for debugging.
- [x] Default native artifacts are written under `target/yulang`.

### Value backend status

- [x] Source-to-runtime lowering can feed the value backend, and native value
      object/executable generation works.
- [x] Generated executables can print boxed runtime values, including scalar
      values, strings, lists, tuples, records, variants, raw views, and basic
      range/splice results.
- [x] Scalar literals and common numeric/boolean/string primitives run through
      runtime helper symbols.
- [x] Local `my` bindings and top-level non-function bindings can be evaluated
      by the value backend.
- [x] List literals, list merge, length, index, raw view, range index, and
      splice work.
- [x] Tuple, record, record field selection, record spread expressions, and
      variant construction work.
- [x] Effect-free `if` and the current pattern-match subset work through
      branch/jump lowering.
- [x] Literal, tuple, variant, list, record, and record-spread pattern tests are
      covered in the value backend when their guards stay inside the
      value-backend expression subset.
- [x] Native-control eval, native ABI eval, and value-backend Cranelift share a
      VM comparison harness for boxed `VmValue` roots.
- [x] Non-escaping closure allocation, closure environment loads, indirect
      closure calls, partial application wrappers, and branch-carried closure
      handles work in the current value-backend subset.
- [x] Small std higher-order list programs (`map`, `filter`, `fold`) run through
      the value executable path when they stay inside the supported value subset.
- [ ] General multi-block control flow outside the current branch/jump subset
      is not supported in the value backend.
- [ ] Closure values can be called after flowing through the value backend, but
      printable closure roots and closures embedded as ordinary structural
      runtime values still route to the CPS representation backend.
- [ ] Generic runtime value layout is still backed by `VmValue`; compact native
      representations are not finalized.

### CPS representation backend status

- [x] Pure scalar CPS programs, primitive calls, direct calls, conditionals,
      `case` guards, and `sub` / `return`-style control can compile and run
      through the Cranelift CPS representation path.
- [x] Small source-defined algebraic effects and multi-shot resumptions work in
      the CPS/CPS-repr interpreters and in the scalar Cranelift prototype.
- [x] Handler entry continuations receive captured environments, and handler
      arms are selected through a dynamic handler stack that crosses function
      boundaries.
- [x] Handler-frame guard snapshots, `LocalPushId` / `PeekId` / `FindId`, and
      `AddId` blocked-effect boundaries are represented in CPS and honored by
      handler selection.
- [x] Thunks and resumptions carry handler-stack and guard-stack snapshots in
      the scalar prototype.
- [x] Thunk boundary masks stay attached to thunk pointers through direct force,
      list index, record field selection, and variant payload projection, so
      hidden callback effects still skip blocked inner handlers.
- [x] `ResumeWithHandler` can rebase captured return frames under a freshly
      installed handler.
- [x] Prototype heap handles cover strings, tuples, lists, records, variants,
      closure pointers, thunk pointers, and resumption pointers in the CPS repr
      path.
- [x] String/list/range primitives, conversions, and small host console effects
      are handled through shared runtime helpers or CPS repr helper symbols.
- [x] First-class lambdas, captured closures, partial applications, and closures
      selected from records/lists can be created and called through the CPS repr
      executable path.
- [x] Callback values can be stored in lists, recovered with `std::list::index_raw`,
      and called without losing local handler hygiene on the forced CPS repr path.
- [x] Type-converted thunk values can be stored in lists, indexed back out,
      forced with `BindHere`, and run through CPS lowering and Cranelift.
- [x] Lazy operator results in tuple/list value positions are covered by the
      forced CPS repr executable path without leaking visible thunk handles.
- [x] Lazy operator results in record fields and variant payloads are covered by
      the same forced CPS repr executable path.
- [x] Record spread expressions are covered by the CPS repr executable path.
- [x] CPS repr lowering covers tuple, list, list-spread, record,
      record-spread, record-default, guarded, and variant payload pattern tests
      in `case` arms for the source-shaped regression path.
- [x] Top-level destructuring `my` bindings that lower to self-shadowing
      structural `case` bindings, including record-spread rest bindings, run
      through the default native CLI by routing to CPS repr with a structured
      `structural pattern binding` reason.
- [x] `std::junction`, finite-list `for` loops with `last` / `next`, mutable
      reference update, and `std::undet` `.once` / `.list` / `.logic` over
      finite-list choices run through the CPS repr executable path for covered
      observable roots.
- [x] Callback return hygiene is covered by source regressions: direct `f()`
      inside an inner `sub` is captured there, while callback `h()` escapes to
      the caller's `sub`.
- [x] Non-scalar CPS return values that use prototype heap handles print as
      Yulang-like values in generated CPS executables.
- [ ] General returned/stored effectful thunks still need more source-shaped
      coverage outside the current scalar/prototype subset.
- [ ] Forced value-backend execution still has a nullary-binding crash for the
      same top-level destructuring shape; the default native CLI avoids it.
- [ ] General closures and heap value lanes are still prototype
      representations, not finalized native runtime layout.
- [ ] The CPS representation backend is the effectful native mainline, but it is
      not yet a complete replacement for the VM.

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

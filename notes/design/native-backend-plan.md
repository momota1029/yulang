# Native Backend Plan

This note sketches the first native-code path for Yulang.

The goal is not to replace the current VM immediately.  The VM remains the
behavioral oracle while a small, explicit control representation is added beside
it and compiled through Cranelift.

## Goals

- Compile a small monomorphic subset to native code.
- Keep VM execution as the reference result for every native milestone.
- Split compile time and generated-code runtime in benchmarks.
- Make control flow explicit before touching Cranelift.
- Keep algebraic effects in the design, but outside the first compiled subset.
- Avoid optimizing around the playground-specific Wasm interpreter limits.

## Non-Goals

- Do not compile all runtime IR forms in the first slice.
- Do not remove or rewrite the VM.
- Do not use native backend work as a shortcut around static-analysis bugs.
- Do not add a second type inference or monomorphization path.
- Do not make Cranelift see high-level effect handlers directly.

## Pipeline

The proposed pipeline starts after the existing runtime path has already done
lowering and monomorphization:

```text
source
  -> infer/lower
  -> principal core IR
  -> typed runtime IR
  -> monomorphized runtime IR
  -> native control IR
  -> layout / ABI lowering
  -> Cranelift IR
  -> JIT / object
```

Important boundary:

- Native backend consumes monomorphic runtime IR.
- Runtime IR validation still runs before native lowering.
- If native lowering cannot handle a function or root, it reports an unsupported
  native-subset diagnostic and the CLI can still run the VM.

## First Subset

The first subset should be intentionally small.

Allowed:

- integer, float, bool, unit, and string literals;
- primitive numeric and string operations that already have runtime primitive
  symbols;
- direct calls to monomorphic functions;
- local `let` bindings;
- `if`;
- tuples if representation is straightforward;
- simple records and variants only after layout is explicit;
- pure root expressions with no residual host or user effects.

Excluded from the first compiled milestone:

- algebraic effect operations;
- handlers and resumptions;
- thunks used for effectful computation;
- closures with captured environments;
- generic or residual-polymorphic bindings;
- host requests such as console and filesystem;
- nondeterministic search;
- mutable references and projection updates.

The first success condition is a small set of pure examples where:

```text
VM result == native result
```

for every root expression.

## Control IR

Cranelift should not be the first place where Yulang control flow becomes
explicit.  Add a small native control IR first.

Suggested shape:

```rust
NativeModule
  functions: Vec<NativeFunction>
  roots: Vec<NativeRoot>

NativeFunction
  name
  params
  result
  blocks: Vec<NativeBlock>

NativeBlock
  params
  stmts: Vec<NativeStmt>
  terminator: NativeTerminator
```

Early statement forms:

- assign literal;
- assign primitive operation;
- assign direct call;
- construct tuple/record/variant if supported;
- project tuple/record field if supported.

Early terminators:

- return value;
- jump block(args);
- branch bool then_block(args) else_block(args).

This is closer to ANF plus blocks than full CPS.  That is enough for the first
slice and still leaves a path to effect continuations later.

## Effects Later

Algebraic effects should lower to explicit continuation objects or continuation
blocks, not directly to recursive VM-style interpreter frames.

Later design questions:

- Is a resumption a heap-allocated continuation object, a stack segment, or a
  function pointer plus environment?
- Can one-shot continuations use a cheaper representation than multi-shot
  continuations?
- Which handlers need multi-shot resumptions?  `std::undet` does.
- How do `bind_here`, effect ids, and handler hygiene map onto native control?
- Which host requests cross the native boundary and which stay interpreted?

The recent `std::undet.once` Wasm stack issue is relevant here: the current VM
stores continuation frames with owned `Expr`, handler arms, and `Env` data.  The
native path should not copy source/runtime expression trees as part of ordinary
resumption.

## Runtime Representation

The first native representation should be boring and explicit.

Initial candidates:

- `int`: machine signed integer matching current runtime semantics only after
  the exact representation is confirmed;
- `float`: native double;
- `bool`: i8/i1 lowered as needed;
- `unit`: zero-sized or ignored value;
- `str`: pointer to runtime string object, not raw UTF-8 everywhere;
- tuple/record: aggregate layout after field order and ownership are fixed;
- variant: tag plus payload layout after enum representation is fixed.

Open questions:

- Current VM values use high-level Rust structures.  Native code needs a stable
  runtime ABI before complex values can be efficient.
- Strings and lists should probably call runtime helper functions first, then be
  optimized later.
- GC / ownership cannot be postponed forever if native code allocates closures,
  strings, lists, or variants.

## CLI Shape

Add experimental flags only after the control IR exists.

Possible flags:

```text
yulang --native-ir <file>
yulang --native-run <file>
yulang --native-compare <file>
```

`--native-compare` should run VM and native code and fail if formatted root
results differ.  That keeps the early backend honest.

For unsupported programs:

```text
native backend does not support effect handlers yet
```

is better than falling through to a misleading internal error.

## Benchmark Shape

Benchmarks should report at least:

- source/infer/lower time;
- runtime lower time;
- monomorphize time;
- native control lowering time;
- Cranelift compile time;
- VM eval time;
- native eval time.

The benchmark should include:

- a tiny startup case;
- primitive arithmetic;
- direct function calls;
- a branch-heavy pure function;
- one larger pure example once available.

Do not benchmark unsupported effect-heavy examples as native failures.  Keep
those in VM and static-analysis benchmarks until effect continuations are part
of the native subset.

## Implementation Phases

### Phase 0: Design Boundary

- Keep this note and `notes/todo/native-backend.md` aligned.
- Pick the runtime IR boundary.
- Decide whether the first control IR lives in `yulang-runtime` or a new crate.

Recommended first crate shape:

```text
crates/yulang-native/
  src/control_ir.rs
  src/lower.rs
  src/validate.rs
  src/compare.rs
```

Cranelift-specific code can stay behind a feature or later module so the control
IR can be tested before native codegen.

### Phase 1: Native Control IR

- Define native control IR types.
- Lower a pure monomorphic root expression to control IR.
- Validate no unsupported runtime IR forms appear.
- Add tests that print or structurally compare control IR.

Success condition:

- A pure arithmetic root can lower to native control IR.

### Phase 2: VM Compare Harness

- Add a CLI or test helper that runs VM output and native-control interpreter
  output, if a tiny control interpreter is useful.
- Otherwise add a harness that lowers both paths and records unsupported native
  forms cleanly.

Success condition:

- Unsupported native cases fail with explicit unsupported-feature diagnostics.

### Phase 3: Cranelift Prototype

- Add Cranelift dependency.
- Compile primitive arithmetic and direct calls.
- Run one root and compare to VM.

Success condition:

- A tiny pure program runs through Cranelift and matches VM output.

### Phase 4: Representation Growth

- Add strings through runtime helper calls.
- Add tuples/records after layout is fixed.
- Add variants after tag/payload layout is fixed.
- Add closure environments only after direct calls are stable.

Success condition:

- Several pure examples run natively with VM comparison.

### Phase 5: Effects Design Spike

- Design continuation representation.
- Lower a one-shot local effect if possible.
- Keep multi-shot nondeterminism as a separate milestone.

Success condition:

- The design can explain `sub` before trying to explain `std::undet.logic`.

## Risks

- Native codegen can hide language bugs if it becomes a parallel semantics.
  Avoid this by comparing against VM output.
- Runtime value representation can sprawl.  Keep the first slice primitive-heavy.
- Effect continuations can dominate the design.  Keep them explicit but out of
  the first milestone.
- Cranelift integration can distract from control IR.  Build and test control IR
  first.

## Near-Term Next Step

Create the native control IR skeleton and a lowering function that accepts a
monomorphized runtime `Module`, rejects unsupported forms structurally, and
lowers one pure arithmetic root.

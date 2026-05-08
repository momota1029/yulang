# CPS / Effect Lowering Plan

This note sketches the effect-aware lowering path that should exist before a
serious Cranelift backend for full Yulang.

The current `crates/yulang-native` control IR is useful as a pure first-order
debug path.  It is not the place to represent closures, handlers, or
multi-shot resumptions directly.

For the effectful backend, the likely order is:

```text
monomorphized runtime IR
  -> effect-aware CPS / continuation lowering
  -> closure conversion
  -> representation / ABI lowering
  -> Cranelift IR
```

## Goals

- Make effect control flow explicit before closure conversion.
- Represent handler boundaries and resumptions without copying runtime `Expr`
  trees as ordinary execution state.
- Treat multi-shot continuations as a primary design constraint from the first
  CPS IR, not as a late extension.
- Use Yulang immutability to make continuation and closure cloning structural:
  share code, environments, closures, and handler contexts by reference.
- Keep direct pure lowering available as a debug and comparison path.
- Keep the current VM as the behavioral oracle until the CPS path has broad
  comparison coverage.
- Make closure conversion consume an already-control-explicit IR, rather than
  guessing future CPS shapes.

## Non-Goals

- Do not force the pure native control IR to become the final CPS IR.
- Do not make Cranelift directly understand high-level Yulang handlers.
- Do not encode closure capture in the current `NativeStmt` forms.
- Do not fix nondeterminism by adding more VM-style continuation cloning.
- Do not add a second type inference or monomorphization path.
- Do not design a one-shot-only CPS IR and retrofit multi-shot later.

## Immutability Assumption

Yulang source-level values, closures, and environments are immutable.  This is a
major simplifying assumption for multi-shot effects.

The continuation representation should be built around structural sharing:

```text
ContinuationValue
  code: ContinuationCodeId
  env: EnvRef
  handler_context: HandlerContextRef
  shot: OneShot | MultiShot
```

Cloning a multi-shot continuation should copy only small handles:

```text
clone(cont) =
  copy code id
  clone EnvRef
  clone HandlerContextRef
  copy shot kind
```

It should not clone:

- runtime expression trees;
- handler arm bodies;
- closure bodies;
- immutable environment contents;
- immutable closure objects.

This also applies after closure conversion.  A closure value can be cloned by
sharing its code pointer and immutable environment object.

The main caveat is host effects.  Console, filesystem, time, randomness, and
foreign resources are not automatically multi-shot-safe.  The effect system or
native capability layer should eventually distinguish resumable/multi-shot-safe
effects from linear or host-observing effects.

## Why CPS Before Closure Conversion

Yulang effects can observe and invoke the current continuation:

- effect operations suspend the surrounding computation;
- handlers decide how to continue;
- resumptions may be called zero, one, or many times;
- `std::undet` needs multi-shot continuations;
- `bind_here`, effect ids, and handler hygiene affect where a computation may
  resume.

If closure conversion runs first, captured environments are computed for
direct-style lambdas and handler bodies whose eventual continuation shape is
still unstable.  A later CPS pass would then split or rewrap those functions,
forcing environment layout to be redone.

The CPS pass should first decide:

```text
what is a function?
what is a continuation?
what is a handler frame?
what is a resumption value?
```

Closure conversion should then run on that explicit IR and turn the remaining
function-like values into function pointers plus environments.

## Source Boundary

Input should be monomorphized runtime IR.

Required preconditions:

- no residual type parameters in compiled bindings;
- runtime validation has already run;
- principal/runtime evidence has already been inserted;
- effect rows are precise enough to distinguish pure code from effectful code;
- runtime primitive metadata has already been resolved by the normal compiler
  path.

The CPS path should not repair incomplete inference or missing monomorphization.
Those are upstream bugs.

## Target Shape

The first CPS IR does not need to be final Cranelift-shaped code.  It should be
small enough to validate and interpret, but it must already have multi-shot
continuation values.

Possible high-level shape:

```rust
CpsModule
  functions: Vec<CpsFunction>
  continuations: Vec<CpsContinuation>
  handlers: Vec<CpsHandler>
  roots: Vec<CpsRoot>

CpsFunction
  name
  params
  return_cont
  body

CpsContinuation
  name
  params
  body
  shot_kind

CpsContinuationValue
  code
  env
  handler_context
  shot_kind

CpsHandler
  handled_effect
  value_cont
  operation_arms
```

This is intentionally not the same as the current `NativeFunction` block IR.
It may later lower into blocks, but its first job is to make effect control
explicit.

The IR should make continuation cloning explicit enough to test:

```text
resume r v
clone_cont r
```

For an immutable `MultiShot` continuation, `clone_cont` should be a cheap handle
clone, not a deep copy.

## Direct-Style Translation

Pure direct-style expressions can translate into ordinary continuation calls.

Sketch:

```text
lower(expr, k)
```

Where `k` is the continuation receiving the value of `expr`.

Examples:

```text
literal n
  -> k(n)

if cond then a else b
  -> lower(cond, \v ->
       branch v:
         lower(a, k)
         lower(b, k))

direct call f x
  -> lower(x, \v -> call f(v, k))
```

The current pure native control IR already tests pieces of this lowering in
direct-style block form.  That path can stay as a simpler debug route.

## Effect Operation Translation

An effect operation should not be represented as a normal direct call.

It needs access to:

- effect identity;
- payload value;
- current continuation;
- active handler stack / handler environment;
- any effect-id hygiene data needed by `bind_here` / guarded handlers.

Sketch:

```text
perform effect payload k
```

Meaning:

```text
find nearest compatible handler
  -> call operation arm(payload, resume)
```

Where `resume` packages `k` plus the remaining handler context.

Open question:

- Is handler lookup compiled into explicit handler parameters, or represented
  as a runtime helper over a handler stack?

The first CPS spike can use explicit handler parameters even if the later ABI
uses a compact runtime stack.

## Handler Translation

A handler has two different responsibilities:

- handle normal value completion;
- handle an effect request and provide a resumption.

Sketch:

```text
catch body:
  value_pattern -> value_body
  effect_pattern resume_pattern -> effect_body
```

Can lower to:

```text
install handler H around body
lower(body, H.value_cont)
```

When an operation reaches `H`:

```text
H.operation_arm(payload, resume)
```

The resumption must contain enough information to restart the computation after
the operation.  It should not contain owned copies of runtime `Expr` trees.

## Resumption Representation

The crucial design split is one-shot vs multi-shot, but both must be represented
from the beginning.

One-shot continuation:

- can move its captured state;
- may be represented as a stack segment, linear heap object, or direct
  continuation function plus environment;
- calling it twice should be rejected or treated as invalid.

Multi-shot continuation:

- `std::undet` requires this;
- must be cloneable or persistent;
- should share immutable code and immutable environment pieces;
- should share immutable closures captured by the continuation;
- should copy only small handles and branch-local runtime state that truly
  differs per branch.

The current VM clones continuation frames that own `Expr`, handler arms, and
environments.  The CPS path should instead represent code by stable function /
continuation ids and put captured values in compact environment objects.

Because Yulang has no source-level mutable state, the default multi-shot
continuation can be persistent.  One-shot continuations remain useful as an
optimization and for host/linear boundaries, not as the only semantic model.

Sketch:

```text
Resumption {
  continuation: Shared<ContinuationValue>
  handler_context: Shared<HandlerContext>
}

resume(resumption, value):
  invoke resumption.continuation with value under resumption.handler_context

clone(resumption):
  clone shared handles only
```

This should make tiny nondeterminism an early test target, not a late milestone.

## Thunks and `bind_here`

Runtime IR currently uses thunks to represent delayed effectful computation.

CPS lowering should classify thunks:

- pure thunk that can be erased or inlined;
- effectful thunk that becomes a function taking a continuation;
- host/effect request thunk that performs through the active handler context.

`bind_here` should become an explicit boundary operation in CPS, not an
interpreter-only special case.  It likely forces a thunk in the current handler
context and continues with the result.

Open questions:

- Does `bind_here` lower to a normal continuation call with a handler context
  argument?
- Does it need a distinct instruction so effect-id hygiene remains visible?

## Closure Conversion Boundary

Closure conversion should run after CPS.

Input:

- explicit functions;
- explicit continuations;
- explicit handler arms;
- explicit resumption constructors.

Output:

```text
code pointer + environment layout
```

It should handle:

- ordinary closure values;
- continuation closures;
- handler arm closures;
- resumption values;
- recursive and mutually recursive groups.

Since closures are immutable, closure conversion should preserve cheap cloning:

```text
ClosureValue {
  code: FunctionCodeId
  env: EnvRef
}
```

Cloning a closure copies the code id and environment reference.  It should not
copy captured values deeply.

Closure conversion should not need to understand high-level `catch` syntax.
That work belongs to CPS/effect lowering.

## Runtime Representation Boundary

After CPS and closure conversion, representation lowering decides concrete
layouts:

- integer / float / bool / unit;
- string and list runtime helper ABI;
- tuples / records / variants;
- closure object;
- continuation object;
- handler context;
- effect operation descriptor;
- host request boundary.

Cranelift should consume this representation-level IR, not raw runtime IR.

## Relationship to `crates/yulang-native`

`crates/yulang-native` currently provides:

- pure control IR;
- native-control evaluator;
- VM comparison for literals, primitives, `if`, simple binding, direct calls,
  multiple bindings, and small recursion.

That is still useful.

Possible future paths:

```text
runtime IR -> native control IR -> eval/debug
runtime IR -> CPS IR -> closure conversion -> Cranelift
runtime IR -> CPS IR -> closure conversion -> native control/block IR -> Cranelift
```

The pure native control path is not required to be the production path.  It is a
debugging and semantics-checking path.

## Implementation Phases

### Phase 0: Design Boundary

Status: current.

- Keep this note separate from `native-backend-plan.md`.
- Treat current native control IR as a pure debug path.
- Decide the first CPS IR data model before adding code.

### Phase 1: CPS IR Skeleton

- Add a small CPS IR module, likely inside `crates/yulang-native` or a sibling
  crate if it grows.
- Represent functions, continuations, continuation values, handler frames,
  resumptions, and tail calls.
- Include `OneShot` / `MultiShot` in the IR from the start.
- Include explicit cheap clone operations for continuation/resumption handles.
- Add pretty/debug output.
- Add a validator for arity and referenced ids.

Success condition:

- Pure literals, primitive ops, `if`, and direct calls can lower to CPS IR and
  structurally validate without requiring a one-shot-only model.

### Phase 2: CPS Interpreter / Compare

- Add a tiny CPS interpreter.
- Compare CPS interpretation against the VM for the pure subset already covered
  by native control IR.
- Model continuation/resumption values with shared immutable handles, even
  before effect handlers are implemented.

Success condition:

- The same pure cases pass through both debug paths:

```text
VM == native-control eval == CPS eval
```

### Phase 3: Tiny Multi-Shot Effect

- Lower one tiny effect operation and one matching handler where the resumption
  is explicitly `MultiShot`.
- Support a finite nondeterminism-style example before optimizing anything.
- Confirm that resumption clone shares code, closures, environment, and handler
  context.

Success condition:

- A small `std::undet`-style finite program matches the VM without VM-style
  expression-tree cloning.

### Phase 4: One-Shot / Linear Optimization

- Add one-shot continuation marking as an optimization and for linear host
  boundaries.
- Reject or guard double-resume only for continuations proven one-shot.
- Keep multi-shot as the default semantic target for ordinary Yulang effects
  that need it.

Success condition:

- One-shot and multi-shot continuation values can coexist in the CPS
  interpreter with explicit diagnostics for invalid one-shot reuse.

### Phase 5: Closure Conversion

- Run free-variable analysis on CPS IR.
- Lower functions, continuations, handler arms, and resumptions to code pointer
  plus environment layout.
- Preserve structural sharing for immutable closure and continuation envs.
- Add tests for captured values and recursive groups.

Success condition:

- Closure-converted CPS IR can still be interpreted or validated and matches
  the pre-conversion CPS behavior.

### Phase 6: Cranelift Boundary

- Lower closure-converted representation IR to Cranelift.
- Start with pure cases and one-shot effect cases.
- Keep VM comparison and CPS-debug comparison available.

Success condition:

- A small compiled program matches VM output, and failures can be localized to
  CPS lowering, closure conversion, representation lowering, or Cranelift codegen.

## Open Questions

- Does the first CPS IR use named continuation ids, block ids, or both?
- Are handlers explicit parameters on every effectful function, or a runtime
  stack object threaded through effectful calls?
- How are effect ids and handler hygiene represented after CPS?
- Which continuations are statically one-shot?
- What reference representation should `EnvRef`, `HandlerContextRef`, and
  closure envs use before a full GC decision?
- Does closure conversion require a separate recursive-group analysis before
  representation lowering?
- Where does host effect interop sit: CPS operation, runtime helper, or VM
  fallback boundary?
- Which host effects are safe to resume through multi-shot continuations, and
  which require one-shot/linear treatment?

## Near-Term Next Step

Define the CPS IR skeleton with multi-shot continuation values and cheap handle
clone semantics from the start.  The first implementation can still lower the
existing pure subset, but the IR must already be capable of representing the
finite nondeterminism target without redesign.

# Demand-Driven Monomorphization Plan

This is the replacement plan for the current monomorphization loop.  The goal
is not to tidy the existing fixed-point rewriter.  The goal is to build a new
algorithmic core that does not repeatedly rewrite the whole runtime tree until
types happen to settle.

## Problem

The current monomorphization pass is too heavy and too fragile:

- it rewrites whole expression trees in several directions;
- it depends on fixed-point rounds to propagate information;
- it treats `_` / `Any` as a recoverable runtime shape in too many places;
- it lets thunk shape, effects, role calls, and casts all influence each other
  inside the same rewrite loop;
- it can leave `Thunk[..., _]` in generated runtime IR even when call-site
  information should have made the value type concrete.

The failure mode is structural.  Local repairs make individual examples pass,
but they do not remove the need for repeated global repair.

## New Core

Use demand-driven monomorphization.

```text
root expression / exported root
  -> demand(binding, expected runtime type)
  -> instantiate the binding scheme with fresh mono holes
  -> check/lower the binding body against the demand
  -> direct calls create new demands
  -> each solved demand emits exactly one specialized binding
```

The important change is that specialization is no longer a global rewrite
search.  A concrete use site asks for a concrete version of a binding.  The
body is checked once under that expected type and emits more demands for the
bindings it calls.

## Type Discipline

`Any` must not be a normal runtime value type inside the new engine.

The new engine distinguishes:

- source wildcard / explicit `_`
- fresh monomorphization hole
- principal type variable
- concrete runtime type
- wildcard effect annotation

When a demand enters the engine, `Any` becomes a fresh monomorphization hole in
the demand signature.  It may later be solved by bidirectional checking.  If it
is still unsolved when a binding is emitted, that is a monomorphization error,
not something for VM erase to tolerate.

## Bidirectional Body Check

The body processor should be a checker, not a tree repair pass:

- `synth(expr) -> typed expr, type`
- `check(expr, expected) -> typed expr`
- lambda checks against an expected function type;
- application synthesizes the callee, checks the argument against the parameter,
  and creates a demand for generic callees;
- `Thunk` and `BindHere` are introduced or preserved only at the check boundary;
- handlers consume effects from principal type information and annotations, not
  from handler-body guessing;
- casts remain only when concrete source/target types disagree.

## Worklist Model

The worklist owns all specialization state:

- `DemandKey` deduplicates `(binding path, demand signature)`;
- `DemandQueue` preserves insertion order for deterministic output;
- each queued demand is processed once;
- processing may enqueue child demands;
- emitted bindings are reachable by construction, so pruning becomes a safety
  check rather than a normal cleanup pass.

## Migration Strategy

Do this beside the old implementation:

1. Add `monomorphize2` with demand signatures and a deterministic queue.
2. Add tests proving `Any` is represented as a mono hole in demand space.
3. Add a checker skeleton that handles variables, lambdas, applications, and
   literals without changing the public compiler path.
4. Teach the checker to emit demands for direct generic calls.
5. Add comparison tests for tiny functions and primitive calls.
6. Move constructor and primitive specialization into demand processing.
7. Move role method resolution into demand processing.
8. Move thunk/effect/hygiene preservation into the checker.
9. Run `examples/03_for_last.yu` and `examples/06_undet_once.yu` through the new
   path and require no residual `Thunk[..., _]` in strict value-type audit.
10. Replace the old fixed-point pipeline only after the new path handles the
    current VM example set.

## First Implementation Slice

The first slice is intentionally small:

- create `crates/yulang-runtime/src/monomorphize2`;
- define `Demand`, `DemandKey`, `DemandSignature`, and `DemandQueue`;
- canonicalize `RuntimeType::Core(Any)` into `DemandSignature::Hole`;
- keep effect slots separate from value slots in the signature;
- add tests for deterministic deduplication and no raw `Any` in demand keys.

This gives the rest of the implementation a safe place to attach without
touching the old fixed-point pipeline yet.

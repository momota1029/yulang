# Native GC Runtime Plan

This note adopts the post-prototype native runtime layout plan. The goal is not
to make the current `VmValue`-backed prototype collectible. The goal is to move
native execution to a dedicated value word, object layout, root discipline, and
MMTk-backed heap.

The VM remains the semantic oracle. The native runtime gets its own object
model because CPS representation allocates many small continuations, thunks,
environments, and handler frames on hot paths.

## Motivation

The native effects backend is centered on CPS representation. Ordinary
execution creates small continuation-shaped objects frequently:

- resumption objects;
- continuation environments;
- thunks and thunk environments;
- closure environments;
- handler frames and return frames;
- structural values crossing effect boundaries.

These objects must be cheap to create. Per-object ownership management or
reference counting would put cost directly on continuation creation and update
paths. A GC-backed heap keeps the allocation fast path thin and moves
reclamation out of the immediate continuation construction path.

MMTk is the preferred substrate because Yulang should reuse an existing GC
framework instead of baking a collector design into the native runtime. The
first goal is a traceable runtime object model, not a sophisticated collector
policy.

A GC-backed heap also keeps open a language design where mutable references are
not required as a primitive mechanism. Updates can be represented with new
values, continuations, and structural sharing. That design point may be slower
than mutable references, but it keeps the semantic model simpler while the
language is still evolving.

## Non-Goals

- Do not make `runtime::VmValue` the native heap object model.
- Do not rewrite the VM around MMTk.
- Do not require all native optimizations to wait for GC.
- Do not add a moving/generational collector policy as the first milestone.
- Do not rely on conservative stack scanning for JIT values.
- Do not key layout or tracing behavior on source module paths or function
  names.

## Value Word

The native runtime uses one machine-word value representation:

```text
YValue
  i63 immediate
  heap object reference
  small immediate values such as unit and bool
```

`YValue` is the ordinary payload carried by CPS continuations, closure
environments, tuples, lists, records, variants, and helper calls. The current
`RuntimeValuePtr` and transitional opaque `i64` lanes should converge toward
this value word where possible.

The tag scheme must be fixed before object layout work begins. It must satisfy:

- immediate integers are recognizable without touching the heap;
- heap references are recognizable for precise root scanning;
- bool/unit immediates do not alias valid heap references;
- MMTk object alignment assumptions are explicit;
- JIT code and Rust helpers use the same predicates.

Avoid calling this representation "zero cost". The target is near
bump-allocation cost for heap objects and word-copy cost for immediate values.

## Integer Representation

The language-level integer remains arbitrary precision. Native uses:

```text
int
  small: tagged i63 immediate
  big: heap BigInt object
```

Fast paths operate on i63 immediates. Arithmetic overflows allocate or call into
a helper that returns a `BigInt` object. Big integers are normal GC objects and
participate in tracing like other heap values.

The first bigint milestone does not need a complete arithmetic library. It
should cover enough to validate the representation:

- i63 construction and debug formatting;
- overflow promotion to `BigInt`;
- `BigInt` debug formatting;
- equality and ordering;
- add/sub/mul on representative cases.

Division, full parsing, and optimized bigint algorithms can follow after the
value word and root discipline are stable.

## Heap Objects

The first native heap object set should include:

- `BigInt`;
- string, bytes, and path values;
- tuple;
- record;
- variant;
- list node or list tree;
- closure;
- thunk;
- resumption;
- continuation environment;
- handler frame;
- return frame;

Every object has a native header that records enough information for tracing
and debugging. The exact header shape belongs to the implementation spike, but
the responsibility is fixed: allocation, object kind dispatch, field tracing,
and debug projection must not depend on `VmValue`.

## Roots And Safepoints

GC correctness depends on a precise live-value boundary between JIT code and
Rust helpers.

Root sources include:

- root function parameters and return values;
- live CPS continuation parameters;
- temporary values live across helper calls;
- closure/thunk/resumption environment slots;
- handler stack, return frame stack, guard stack, and pending abort/scope-return
  state;
- native runtime context state for host requests and debug printing.

The first implementation should use an explicit root stack or shadow stack.
Each helper that can allocate must either receive only already-rooted values or
establish roots before allocation. A collection-every-allocation stress mode is
required before the GC path becomes default.

## JIT ABI Direction

The existing CPS repr ABI lanes are useful as a transition boundary, but the
long-term shape should reduce the number of pointer-like special lanes.

Target direction:

```text
scalar control lanes:
  native bool/branch condition where proven unboxed
  native float where proven unboxed

ordinary value lane:
  YValue

special internal lanes:
  function/code id
  prompt/guard/eval ids
  raw helper-only indexes or lengths
```

Closure, thunk, resumption, tuple, list, record, variant, string, bigint, and
boxed scalar values should all be ordinary `YValue` payloads unless a local
optimization proves that they do not escape.

## Migration Plan

1. Add a design-only boundary in docs and tasks.
2. Spike `YValue` tagging and MMTk object allocation in isolation from the
   existing default native path.
3. Add a `GcRuntimeContext` alongside the current prototype runtime context.
4. Implement object headers, `BigInt`, tuple, closure/thunk/resumption, and
   continuation environment tracing.
5. Port a small CPS repr executable smoke test to the GC context behind a flag.
6. Add explicit root stack support for JIT-to-helper calls.
7. Add collection stress mode and run covered native regression cases through
   it.
8. Move structural helper allocation sites from prototype handles to `YValue`.
9. Remove or quarantine the old `VmValue`-backed prototype heap once the covered
   effects subset passes on the GC path.

## Test Strategy

The GC path needs tests that expose missing roots rather than only final value
shape.

Required test classes:

- allocation smoke test for each heap object kind;
- collection-every-allocation test for tuple/list/record/string values;
- collection-every-allocation test for closure/thunk/resumption capture;
- recursive handler and multi-shot nondeterminism under forced collection;
- i63 overflow promotion and bigint debug/equality tests;
- native-vs-VM source regressions for covered effects examples.

The release gate should keep the non-GC native path passing during migration.
The GC path becomes part of the gate only after it covers the documented native
effects subset.

## Open Questions

- Which exact MMTk plan should be used for the first spike?
- How much of the JIT frame state is represented by a shadow stack versus
  explicit helper arguments?
- Which objects, if any, should be stack/SSA allocated before the GC path is
  complete?
- How should host request state expose roots while a request is suspended?
- Where should debug projection from `YValue` to user-facing display live?

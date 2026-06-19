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

1. Add a design-only boundary in docs and tasks. **Done 2026-05-18.**
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

### Progress 2026-05-18

`crates/yulang-native/src/gc_runtime.rs` now contains the first isolated runtime
object model spike:

- `YValue` with `i63` immediates, bool/unit immediates, and aligned heap-object
  references;
- `GcRuntimeContext` beside the prototype `NativeRuntimeContext`;
- native object headers and payload variants for `BigInt`, string/bytes/path,
  tuple/record/variant/list, closure/thunk/resumption, continuation env,
  handler frame, and return frame;
- allocation helpers and smoke coverage for each first-milestone object kind;
- string/list payloads use red-black-tree rope node shapes aligned with the
  existing runtime `StringTree` / `ListTree` operations, so concat/slice helpers
  can avoid baking a flat representation into the object model;
- explicit root stack and trace walk over rooted heap objects;
- `YHeap` allocator boundary with the current `SpikeHeap` implementation, so
  an MMTk heap can replace the spike storage without changing `YValue` callers;
- root frames and temporary-root helper scopes for JIT/helper temporaries;
- allocation stress mode that traces roots before each allocation;
- allocated-heap stats and live root-trace reports, so later MMTk-backed heap
  behavior has a small comparison surface;
- i63 add/sub/mul helper smoke coverage with overflow/underflow promotion to
  heap `BigInt`, plus comparison over the current decimal spike values.
- monomorphic native layout descriptors, interned layout handles, and typed
  heap blocks with raw payload buffers, payload footprint, field offsets, and
  trace bitmaps. This keeps the generic `YValue` object model from becoming the
  only storage shape: after type monomorphization, tuple, closure env,
  continuation env, and stack-frame layouts can keep `i64`/`u64`/`f64`/bool
  fields unboxed while tracing only the `YValue` fields. Stack-frame layouts are
  intentionally rejected by heap allocation, and equal monomorphic layouts are
  shared through the registry instead of copied into every object.
- native symbols for static path and atom identity. `YSymbolTable` maps
  `typed_ir::Path`, `Name`-shaped data, and Ruby-style atom strings to compact
  `YSymbolId` values with stable fingerprints kept for diagnostics and lookup.
  Atom symbols and path symbols are distinct even when their display text
  overlaps. ADT-style tags can use symbol ids instead of carrying full paths
  through runtime payloads, and monomorphic native blocks have a `Symbol` field
  lane for unboxed symbol payload slots. Closed symbol sets can be frozen into a
  collision-checked `hash -> symbol id` lookup as a first step toward a real
  perfect hash table.
- native variant layout helpers. Variant heap blocks can use a `Symbol` tag as
  field 0 in the raw payload, followed by monomorphic typed payload fields. The
  symbol tag is not traced; payload tracing follows the same field-lane bitmap
  as tuple and environment blocks.
- MMTk configuration boundary. `crates/yulang-native/src/mmtk_runtime.rs`
  defines the first always-built MMTk surface, using a single-threaded `NoGC`
  plan as the initial integration target while the Yulang VM binding callbacks
  are still being built.
- MMTk VM binding skeleton. `crates/yulang-native/src/mmtk_binding.rs`
  defines the Yulang binding marker, native object header, `YValue` slot
  representation, memory slice, object-size callback, trace-slot scanner, and
  the required collection/reference/active-plan callback surface for the
  initial `NoGC` spike.
- first `MmtkHeap` prototype. `crates/yulang-native/src/mmtk_runtime.rs`
  implements the `YHeap` boundary using MMTk allocation for object headers and
  trace slots. The current semantic `YObject` payload also lives in the MMTk raw
  payload area, and `MmtkHeap::object` projects it from the object reference.
  The heap can also allocate compact raw-payload objects and compact
  `NativeHeapBlock` payloads, including closure/thunk/resumption/env/frame
  payloads, keeping layout-offset field reads separate from semantic `YObject`
  projection.
- split heap read surface. `YHeap` now exposes object-header and trace-child
  projection separately from full semantic `YObject` projection, so tracing and
  stats can remain stable while individual payload kinds move to compact raw
  fields.
- first native helper context over MMTk. `MmtkNativeRuntimeContext` wraps
  `GcRuntimeContext<MmtkHeap>` and exposes raw `YValue` word helpers for unit,
  bool, int arithmetic/compare, scalar string conversions, red-black-tree string
  construction/concat/index/range/splice/length/equality, compact bytes/path
  conversion helpers, compact tuple/record/variant construction/access, and
  chunked red-black list construction/access/view/range/splice, including
  record default/has/without.
  The C ABI smoke path gives later helper-symbol wiring a concrete target
  without forcing the JIT boundary to be chosen yet.
- parallel MMTk CPS helper symbols. `runtime_symbols.rs` registers
  `yulang_mmtk_cps_*` names for a future all-`YValue` CPS lane. This is
  intentionally separate from the existing `yulang_cps_*` helper ABI, because
  the current CPS i64 path still passes plain scalar i64 values and prototype
  heap handles.
- minimal JIT smoke for the future lane. A Cranelift test builds
  one hand-written function that calls `yulang_mmtk_cps_*` helpers through the
  JIT symbol table and round-trips `YValue` string/bytes/tuple values. This
  fixes the helper-symbol boundary without switching normal CPS lowering yet.
- opt-in CPS repr primitive lane. `CpsReprCraneliftOptions` can route the first
  current runtime primitive family and tuple/record/variant structural
  statements through the MMTk helper set where the boundary already carries
  `YValue` payloads while leaving the default CPS backend on the prototype
  helper ABI. In this opt-in lane, Yulang `int`, bool, and unit values already
  flow as tagged `YValue` words through primitive calls and branch conditions.
  Float operations still use unboxed `f64` inputs and box boolean comparison
  results back into `YValue`. Fixed-width `i64`/`u64` lanes are native layout
  support only until Yulang grows explicit source-level types for them.
- benchmark CLI entrypoint. `yulang run --mmtk` routes source execution through
  this MMTk `YValue` primitive lane and fails on unsupported shapes instead of
  falling back to the prototype native runtime.

This is only partially MMTk-backed. The next implementation step is to replace
remaining transitional semantic payload users with compact raw/native-block
paths where that keeps tracing precise, while keeping the current helper
context as a JIT-less smoke harness.

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

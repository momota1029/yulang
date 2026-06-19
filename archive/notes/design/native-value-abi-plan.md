# Native Value ABI Plan

This note fixed the next boundary after the old `i64` Cranelift scalar
prototype. It remains useful as the history of the opaque runtime value pointer
step. The adopted post-prototype runtime layout is now
`archive/notes/design/native-gc-runtime-plan.md`.

The current prototype can compare:

```text
VM value
  == native-control value
  == native ABI eval value
  == Cranelift i64 scalar
```

That is enough for int / bool / unit and a small closure-call subset. It is not
enough for `str`, `list`, `record`, variants, or general closures. Those need a
runtime value representation instead of treating every value as `i64`.

## Near-Term Shape

Keep the scalar path as a fast debug subset, and add a second ABI lane:

```text
NativeAbiRepr
  Unit
  Bool
  Int
  Float
  List(element)
  Tuple([...])
  Record([...])
  RuntimeValuePtr(...)
  ClosurePtr
```

The Cranelift boundary should be explicit about which lane a function uses.
`List(element)` is still a pointer lane at the machine boundary, but the
element representation is tracked so `list<int>` / `list<float>` can become
native later without treating every list as the same opaque value. Do not
silently reinterpret a runtime pointer as an integer result.

## Value Representation

Use an opaque runtime value pointer first:

```text
type yul_value = *mut NativeRuntimeValue
```

The first implementation should be hosted by Rust helpers:

- construct string values;
- concatenate / inspect strings;
- construct list values;
- index / merge lists;
- allocate record values;
- select record fields;
- compare or format values only through helper functions.

This is intentionally not the final high-performance representation. It keeps
Cranelift lowering simple while preserving language behavior.

## Why The Prototype Did Not Tag Everything Immediately

A fully tagged value ABI would be closer to a production VM/JIT, but it forces
these decisions at once:

- integer tagging and overflow policy;
- pointer tagging alignment assumptions;
- GC / arena ownership;
- string/list/record layout;
- closure layout;
- cross-boundary panic/error behavior.

That was too much for the next step at the time. The opaque pointer lane let us
prove the lowering path and call boundaries first.

The next runtime layout step intentionally does tag values. It uses a `YValue`
word with `i63` immediates, heap object references, and small immediates such as
bool/unit, backed by a traceable native heap instead of `VmValue` boxes.

## Ownership

For the prototype:

- allocate values in a per-JIT-run arena owned by `NativeJitModule`;
- pass an arena/context pointer as the first hidden argument to every value-lane
  root/function;
- return `yul_value`;
- keep values alive until the root run finishes;
- do not expose those pointers outside the compare harness except by converting
  them back to `runtime::VmValue`.

This avoided committing to GC before the control path was useful. The CPS repr
effects path is now useful enough that the next stable runtime layout should be
GC-backed rather than extending the prototype arena indefinitely.

## Function Signatures

Scalar-only functions keep the current signature:

```text
(i64, i64, ...) -> i64
```

Value-lane functions use:

```text
(ctx, arg0, arg1, ...) -> yul_value
```

Mixed scalar/value signatures should be avoided initially. If a function touches
heap values, lower all of its parameters/results through the value lane.

## Primitive Lowering

Keep primitive lowering table-driven:

- scalar-supported primitives can stay in Cranelift instructions;
- value-supported primitives lower to Rust helper calls;
- unsupported primitives remain structured errors.

Do not branch on source path or std names in the native backend.

## Records And Variants

Records should start as helper-backed immutable maps/arrays:

- lowering provides stable field names or field indexes;
- construction calls a helper with field descriptors and value pointers;
- selection calls a helper with the field descriptor.

Variants can share the same object representation with a tag plus optional
payload.

## Closure Values

The current hosted closure subset rewrites local closure calls to direct calls
with hidden environment args. General closures need to become heap values:

```text
closure value = { code id, env values }
```

This should be implemented after opaque `yul_value` works for strings/lists,
because closure environments need to store arbitrary values.

## Next Implementation Steps

1. Add a `NativeAbiRepr` analysis that classifies ABI functions/values by
   native representation.
2. Keep `compile_abi_module` scalar-only and add a separate experimental
   `compile_value_abi_module`.
3. Add a small Rust helper surface for `str` construction and concatenation.
4. Add source compare for a string expression once `runtime::VmValue::String`
   can round-trip through the value lane.
5. Extend the same lane to lists, then records.

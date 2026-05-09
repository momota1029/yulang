# Native Value ABI Plan

This note fixes the next boundary after the current `i64` Cranelift scalar
prototype.

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
NativeAbiValue
  ScalarI64
  RuntimeValuePtr
```

The Cranelift boundary should be explicit about which lane a function uses.
Do not silently reinterpret a runtime pointer as an integer result.

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

## Why Not Tag Everything Immediately

A fully tagged value ABI would be closer to a production VM/JIT, but it forces
these decisions at once:

- integer tagging and overflow policy;
- pointer tagging alignment assumptions;
- GC / arena ownership;
- string/list/record layout;
- closure layout;
- cross-boundary panic/error behavior.

That is too much for the next step. The opaque pointer lane lets us prove the
lowering path and call boundaries first.

## Ownership

For the prototype:

- allocate values in a per-JIT-run arena owned by `NativeJitModule`;
- pass an arena/context pointer as the first hidden argument to every value-lane
  root/function;
- return `yul_value`;
- keep values alive until the root run finishes;
- do not expose those pointers outside the compare harness except by converting
  them back to `runtime::VmValue`.

This avoids committing to GC before the control path is useful.

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

1. Add a `NativeAbiValueLane` analysis that classifies functions as
   `ScalarI64` or `RuntimeValuePtr`.
2. Keep `compile_abi_module` scalar-only and add a separate experimental
   `compile_value_abi_module`.
3. Add a small Rust helper surface for `str` construction and concatenation.
4. Add source compare for a string expression once `runtime::VmValue::String`
   can round-trip through the value lane.
5. Extend the same lane to lists, then records.

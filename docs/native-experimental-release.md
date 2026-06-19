# Archived Native Experimental Release Notes

Date: 2026-05-18

Retired from the active workspace: 2026-05-25

This note records the final release-gate stance for the old
`yulang run --native` experimental subset. It is historical: the native backend
was archived before becoming the current user-facing execution path, and the
active CLI no longer exposes `yulang run --native` or `yulang native`.

Use the VM for current execution:

```bash
yulang run path/to/file.yu
yulang run --print-roots path/to/file.yu
```

## Historical Status

On 2026-05-18, the documented native effects subset had a passing release gate
and was ready to be treated as an experimental release candidate. That candidate
was superseded by the 2026-05-25 cleanup that archived `yulang-native`, removed
native CLI dispatch, and refocused the active workspace on the VM plus the new
monomorphize/runtime crate split.

The current archive summary is in
[native-backend.md](native-backend.md). The cleanup handoff is in
[`archive/notes/refactors/finalized-vm-handoff-2026-05-25.md`](../archive/notes/refactors/finalized-vm-handoff-2026-05-25.md).

## Covered Historical Subset

The passing gate covered:

- scalar and runtime-shaped root printing through the native effects path;
- tuple, record, variant, list, string, bytes, path, and range helper values;
- source-defined algebraic effects and multi-shot scalar resumptions;
- non-scalar values returned through recursive handler/resumption chains;
- finite and open-range `for` with local `last` / `next` control;
- `sub` / `return` escaping through finite-list and open-range loops;
- finite-list nondeterminism through `.once`, `.list`, and `.logic`;
- open-range guarded nondeterministic `.once`;
- `std::junction` effectful boolean conditions;
- combined `std::junction` + finite nondeterminism + post-result method calls;
- mutable-reference edit/update, including indexed list updates.

## Historical Limits

- Native was opt-in; `yulang run` still used the VM/interpreter path.
- The VM/interpreter remained the semantic oracle.
- Unsupported native shapes reported native-backend diagnostics instead of
  silently falling back.
- Heap values, closures, thunks, and resumptions still used prototype runtime
  layout pieces.
- Package/cache/build workflow and native artifact lifecycle were prototype
  surfaces.
- Type-surface audit and monomorphization strictness were still active compiler
  hardening work.

## Obsolete Release Gate

These commands were valid only for the archived native workspace state:

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-native
RUSTC_WRAPPER= cargo test -q -p yulang --test native_cli
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_undet_once_open_range_guard_through_cps_repr
RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_junction_method_undet_once_through_cps_repr
RUSTC_WRAPPER= cargo run -q -p yulang -- run --native --print-roots examples/03_for_last.yu
RUSTC_WRAPPER= cargo run -q -p yulang -- run --native --print-roots examples/04_sub_return.yu
RUSTC_WRAPPER= cargo run -q -p yulang -- run --native --print-roots examples/06_undet_once.yu
RUSTC_WRAPPER= cargo run -q -p yulang -- run --native --print-roots examples/07_junction.yu
RUSTC_WRAPPER= cargo run -q -p yulang -- run --native --print-roots examples/10_effect_handler.yu
RUSTC_WRAPPER= cargo run -q -p yulang -- run --native --print-roots examples/showcase.yu
```

The expected smoke outputs were:

```text
examples/03_for_last.yu       -> 5
examples/04_sub_return.yu     -> 5
examples/06_undet_once.yu     -> just (3, 4, 5)
examples/07_junction.yu       -> 1
examples/10_effect_handler.yu -> (9, "3\n6\n")
examples/showcase.yu          -> 7 / [2, 6, 4] / 5 / just 18
```

## Obsolete Publish Plan

The native experimental publish plan was not carried forward as the current
release path. The planned crate order at the time was:

```text
yulang-parser   0.1.2
yulang-typed-ir 0.1.2
yulang-sources  0.1.3
yulang-infer    0.1.3
yulang-editor   0.1.2
yulang-runtime  0.1.1
yulang-native   0.1.1
yulang          0.1.1
yulang-ls       0.1.2
```

`yulang-compile` was not on crates.io yet, and `yulang-wasm` was not
publish-ready because its local workspace dependencies intentionally did not
carry registry version requirements.

## Historical Release Note Draft

```text
Native execution is now available as an opt-in experimental subset via
`yulang run --native`. The interpreter remains the semantic oracle. The native
path covers the documented effects subset, including recursive handler tuple
returns, loop control, finite and open-range nondeterminism, `std::junction`,
mutable references, and native root pretty-printing. Unsupported native shapes
still report native-backend diagnostics instead of silently falling back to the
interpreter.
```

# Native Experimental Release Notes

Date: 2026-05-18

This note records the release stance for the first `yulang run --native`
experimental subset. It is not a compatibility promise for the whole language:
the interpreter remains the semantic oracle, and native execution is still an
opt-in backend.

## Status

The documented native effects subset has a passing release gate and is ready to
be treated as an experimental release candidate.

Use:

```bash
yulang run --native path/to/file.yu
```

The lower-level native command remains available for backend and artifact work:

```bash
yulang native path/to/file.yu
```

## Covered Subset

The covered release-gate subset includes:

- scalar and runtime-shaped root printing through the native effects path;
- tuple, record, variant, list, string, bytes, path, and range helper values;
- source-defined algebraic effects and multi-shot scalar resumptions;
- non-scalar values returned through recursive handler / resumption chains;
- finite and open-range `for` with local `last` / `next` control;
- `sub` / `return` escaping through finite-list and open-range loops;
- finite-list nondeterminism through `.once`, `.list`, and `.logic`;
- open-range guarded nondeterministic `.once`;
- `std::junction` effectful boolean conditions;
- combined `std::junction` + finite nondet + post-result method calls;
- mutable-reference edit / update, including indexed list updates.

The support table in [native-backend.md](native-backend.md) is the source of
truth for the currently documented subset.

## Intentional Limits

- Native is opt-in. `yulang run` still uses the interpreter.
- The interpreter remains the semantic oracle. Native output should be compared
  against `yulang run` when investigating behavior.
- Unsupported native shapes report a native-backend diagnostic. They do not
  silently fall back to the interpreter yet.
- Heap values, closures, thunks, and resumptions still use prototype runtime
  layout pieces rather than a finalized native object model.
- Package/cache/build workflow and native artifact lifecycle are still
  prototype surfaces.
- Type-surface audit and monomorphization strictness remain active compiler
  hardening work, but they are not blockers for this native experimental subset.

## Release Gate

Before tagging a native experimental release, run:

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

The expected smoke outputs are:

```text
examples/03_for_last.yu       -> 5
examples/04_sub_return.yu     -> 5
examples/06_undet_once.yu     -> just (3, 4, 5)
examples/07_junction.yu       -> 1
examples/10_effect_handler.yu -> (9, "3\n6\n")
examples/showcase.yu          -> 7 / [2, 6, 4] / 5 / just 18
```

## Crates.io Publish Order

The current publish bump is based on comparing local package tarballs against
the previously published crates.io tarballs. Publish in dependency order:

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

`yulang-compile` is not on crates.io yet; its local dependency requirements are
updated for this set, but publishing it would be a first release rather than a
version bump. `yulang-wasm` is not publish-ready as a crates.io package because
its local workspace dependencies intentionally do not carry registry version
requirements.

Only `yulang-parser` and `yulang-typed-ir` can pass `cargo publish --dry-run`
before anything is uploaded. Later crates depend on these new versions and need
the earlier crates to exist in the crates.io index before their own dry-run can
resolve registry dependencies.

## Suggested Release Note

```text
Native execution is now available as an opt-in experimental subset via
`yulang run --native`. The interpreter remains the semantic oracle. The native
path covers the documented effects subset, including recursive handler tuple
returns, loop control, finite and open-range nondeterminism, `std::junction`,
mutable references, and native root pretty-printing. Unsupported native shapes
still report native-backend diagnostics instead of silently falling back to the
interpreter.
```

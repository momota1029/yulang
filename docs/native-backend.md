# Yulang Native Backend Archive

This page is a historical note. The Cranelift/MMTk native backend is no longer
part of the active workspace, and the current CLI does not expose
`yulang run --native`, `yulang native`, or `yulang run --mmtk`.

Current execution goes through the VM:

```bash
yulang run program.yu
yulang run --print-roots program.yu
```

For current feature support, see [docs/status.md](status.md). For the
language-level overview, see [docs/language/overview.md](language/overview.md).

## Archive Status

The native backend experiment was archived on 2026-05-25 during the
runtime/monomorphize cleanup:

- the active `crates/yulang-native` crate was moved out of the workspace to the
  local archive at `../yulang-archive/yulang-native`;
- the older `archive/yulang-native` snapshot was moved to
  `../yulang-archive/yulang-native-old`;
- native CLI options and dispatch were removed from `crates/yulang`;
- the old runtime monomorphize facade and legacy monomorphize pipeline were
  archived in the same cleanup.

The detailed handoff for that cleanup is
[`notes/refactors/finalized-vm-handoff-2026-05-25.md`](../notes/refactors/finalized-vm-handoff-2026-05-25.md).

## What The Experiment Covered

The archived backend had two main lines:

- a pure-subset Cranelift path for first-order scalar/data programs and backend
  speed checks;
- an effect-aware CPS path for algebraic effects, handlers, resumptions,
  finite nondeterminism, loop control, local returns, and prototype heap values.

The 2026-05-18 gate covered the documented experimental subset:

- scalar and runtime-shaped root printing;
- tuple, record, variant, list, string, bytes, path, and range helper values;
- source-defined algebraic effects and multi-shot scalar resumptions;
- non-scalar values returned through recursive handler/resumption chains;
- finite and open-range `for` with local `last` / `next` control;
- `sub` / `return` escaping through loops;
- finite-list nondeterminism through `.once`, `.list`, and `.logic`;
- open-range guarded nondeterministic `.once`;
- `std::junction` effectful boolean conditions;
- combined `std::junction` + finite nondeterminism + method-call roots;
- mutable-reference edit/update, including indexed list updates.

That subset passed as an experiment, but it did not become the current user
execution surface.

## Why It Was Retired

The native path was useful research, but it was not the right active surface to
carry while the compiler was moving:

- the VM was already a better day-to-day execution target;
- the native path did not meet the performance bar consistently enough to justify
  the maintenance cost;
- the runtime type surface and monomorphize pipeline needed a smaller, stricter
  core before another codegen backend could be healthy;
- MMTk and `YValue` work clarified useful runtime-layout ideas, but the active
  VM/runtime path was the better place to stabilize semantics first.

The archived code remains useful as design evidence for future execution work,
especially around CPS optimization, handler/resumption representation, and
compact runtime value layout.

## Historical Commands

These commands are historical and do not work in the active workspace:

```bash
yulang run --native path/to/file.yu
yulang run --native --native-backend pure path/to/file.yu
yulang run --mmtk path/to/file.yu
yulang native path/to/file.yu
```

The active equivalents for user-facing behavior are VM commands:

```bash
yulang run path/to/file.yu
yulang run --print-roots path/to/file.yu
```

## Related Notes

- [docs/native-experimental-release.md](native-experimental-release.md):
  archived release-gate note for the 2026-05-18 opt-in subset.
- [`tasks/done/2026-05-14-native-backend-history.md`](../tasks/done/2026-05-14-native-backend-history.md):
  milestone history before the final archive cleanup.
- [`notes/design/native-backend-plan.md`](../notes/design/native-backend-plan.md):
  original native backend plan.
- [`notes/design/cps-effect-lowering-plan.md`](../notes/design/cps-effect-lowering-plan.md):
  CPS/effect lowering plan.
- [`notes/design/native-gc-runtime-plan.md`](../notes/design/native-gc-runtime-plan.md):
  native `YValue` / GC runtime plan.
- [`notes/design/native-direct-style-islands.md`](../notes/design/native-direct-style-islands.md):
  direct-style / SSA island optimization direction.

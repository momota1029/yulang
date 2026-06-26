# Yulang Cache Architecture

This note summarizes the active CLI cache routes. It is not a package manager
specification; realm/band identity is still being integrated.

The cache stores compiler artifacts, not program output. A cached run still
collects source files, validates cache keys, and executes the resulting program.

## Artifact layers

Yulang currently uses three persistent artifact layers:

| Extension | Scope | Main purpose |
| --- | --- | --- |
| `.yucu` | full source set, std prefix, source-unit prefix, or merged prefix | Reuse compiled syntax / namespace / lowering / typed / runtime surfaces. |
| `.yuir` | exact full source set | Reuse the principal poly IR after inference. |
| `.yuvm` | exact full source set | Reuse the final control-VM program after specialization and VM lowering. |

`.yuir` and `.yuvm` are exact whole-program artifacts. They are fastest when
the complete source set is unchanged.

`.yucu` stands for "Yulang compiled unit". It is the incremental layer. It can
be used as an exact full-source artifact, but it can also be imported as a
prefix so the compiler only lowers and infers the changed suffix.

## What a `.yucu` contains

A compiled-unit artifact is split into surfaces:

- syntax surface: module syntax exports such as operators and generated parent
  module records;
- namespace surface: modules, values, types, imports, exports, and visibility;
- lowering surface: stable links from namespace symbols to runtime-facing
  source definitions;
- typed surface: public value schemes in a compiled type arena;
- runtime surface: poly runtime definitions, labels, roots, and metadata;
- external runtime reference table: stable references to already-imported
  prefix definitions needed by a dependent suffix.

The split matters because arena-local IDs are not stable across units. Merging
or extending compiled units must allocate fresh target IDs and remap every
surface through that mapping. The CLI does not concatenate `.yucu` payloads.

## Runtime routes

With `--runtime-phase-timings`, `run.cache` reports the route used by the CLI:

| Route | Meaning |
| --- | --- |
| `control-hit` | Exact `.yuvm` hit. |
| `poly-hit` | Exact `.yuir` hit; specialization and VM lowering still run. |
| `compiled-unit-hit` | Exact full-source `.yucu` hit; `.yuir` is rebuilt from surfaces. |
| `std-prefix-hit` | Cached std `.yucu` is imported as the prefix. |
| `std-prefix-build` | Std prefix `.yucu` is built first, then imported. |
| `source-unit-prefix-hit` | One cached source-unit closure is imported as the prefix. |
| `merged-source-unit-prefix-hit` | Several independent cached prefixes are merged and imported. |
| `full-miss` | Fresh compile from source. |
| `error-fallback` | Cache read failed and the compiler fell back to source. |

The normal build path is conservative:

1. try exact `.yuvm` for `run`;
2. try exact `.yuir`;
3. try exact full-source `.yucu`;
4. try std/source-unit prefix `.yucu`;
5. compile from source and write fresh artifacts.

## Source-unit prefix reuse

The source collector builds dependency-ordered source compilation units. A
non-root unit can be cached as a `.yucu` and reused by a later run when the
entry or local suffix changed but that unit did not.

Current behavior is intentionally conservative:

- dependency-bearing non-root units are stored as dependency-closure artifacts;
- independent cached prefixes can be merged into one synthetic prefix artifact;
- overlapping closure artifacts are not merged together;
- the root / changed suffix remains source-backed so diagnostics and root
  expression output stay conservative.

This already improves local edit cycles because the compiler can skip lowering
and inference for unchanged std or dependency modules. It does not remove the
clean-build solver cost.

## External references

When a suffix is lowered against a compiled prefix, its runtime graph may refer
to prefix definitions. Those references cannot be serialized as raw `DefId`s,
because `DefId` values are arena-local.

The external reference table records the stable parts currently needed by the
import path:

- modules and values by namespace path;
- type field methods by owner type path, field name, and receiver kind;
- casts by source type path, target type path, and ordinal.

Some metadata, such as role impl candidates and argument effect contracts, is
reused from the already-imported prefix rather than duplicated into the suffix
artifact. Cache canaries cover effect operations, constructors, field methods,
casts, role impls, and argument effect contracts.

The remaining long-term step is a finer dependency artifact route that imports
dependency artifacts first, then imports a dependent unit whose external
references are all explained by the prefix. Until that is fully covered, the
dependency-closure route stays the default.

## Operational notes

- `yulang cache path` prints the user cache root.
- `yulang cache stats` summarizes cache contents.
- `yulang cache clear` removes the user cache root.
- `--no-cache` disables cache reads and writes for one command.

Cache failure is not a language error. Invalid, old, or unreadable artifacts are
discarded or skipped, then the compiler falls back to source.

## Related documents

- `spec/2026-06-14-control-artifact-cache.md` defines the pipeline artifact
  cache semantics.
- `notes/design/2026-06-26-compiled-unit-surface-merge.md` records the
  compiled-unit merge design and current implementation status.
- `notes/benchmarks/2026-06-26-compiled-unit-cache-speedup.md` records the
  speedup and remaining bottlenecks from the 2026-06-26 cache work.
- `notes/design/source-realm-band-plan.md` defines the realm/band identity
  model that should eventually become part of cache keys.

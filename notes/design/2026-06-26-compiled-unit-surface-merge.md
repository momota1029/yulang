# Compiled-unit surface merge plan

This note defines the next step after the single-prefix source-unit cache.

The current CLI can reuse one cached source-unit `.yuunit` as a lowering prefix.
When multiple independent leaf units are cached, the CLI selects one
dependency-free unit and lowers the rest from source. This avoids a full compile
without merging compiled surfaces.

True multi-prefix reuse needs a real compiled-surface merge. It must not be
implemented by concatenating `.yuunit` artifacts in the CLI.

## Current Invariant

`BodyLoweringPrefix::from_compiled_unit_surfaces` accepts exactly one compiled
unit:

```text
CompiledSyntaxSurface
CompiledNamespaceSurface
CompiledLoweringSurface
CompiledRuntimeSurface
```

The prefix builder:

1. imports one `CompiledRuntimeSurface` into a fresh `poly::Arena`;
2. receives one `CompiledRuntimeImport` mapping source `DefId`s to target
   `DefId`s;
3. rebuilds one `ModuleTable` from one namespace/lowering surface pair and the
   matching runtime import.

Therefore all IDs inside these surfaces are unit-local unless explicitly
remapped.

## Why Concatenation Is Unsound

Independent source-unit artifacts can reuse the same internal ID ranges:

- namespace module IDs;
- namespace value/type symbols;
- lowering surface symbol references;
- runtime `DefId`, `ExprId`, `PatId`, `RefId`, and `SelectId`;
- typed-surface type arena IDs, type variables, and subtract IDs;
- syntax surface module records for synthetic parent modules.

Appending vectors would make two unrelated definitions appear to share the same
identity. The bug may not show up on simple value-only examples, but it can
miswire:

- constructor payload owners;
- act operation definitions;
- type/act/role methods;
- imported value/type/module views;
- public typed schemes;
- runtime module/value definitions;
- syntax exports used by downstream parsing.

The merge must be path-based at namespace boundaries and ID-based only after a
fresh target ID has been allocated.

## Merge Target

The first full implementation should produce a single synthetic compiled-unit
artifact:

```text
MergedCompiledUnit {
  manifest
  syntax
  namespace
  lowering
  typed
  runtime
  errors
}
```

This can then reuse the existing single-prefix lowering path:

```text
build_poly_from_compiled_unit_prefix_and_collected_sources(merged, suffix)
```

That keeps the CLI small and makes the merge reusable by future realm/band
builds.

## Required Remaps

### Syntax

`CompiledSyntaxSurface` should merge by module path.

Rules:

- keep one record per module path;
- error on conflicting syntax exports for the same module path;
- preserve deterministic order by module path depth and lexical path;
- include synthetic parent module records when they contribute exported module
  declarations needed by suffix parsing.

### Namespace

`CompiledNamespaceSurface` needs fresh global IDs:

```text
old (unit_index, module_id) -> merged module_id
old (unit_index, value_symbol) -> merged value_symbol
old (unit_index, type_symbol)  -> merged type_symbol
```

Rules:

- modules merge by path;
- value/type declarations merge by `(module path, name, order, visibility,
  kind)`;
- exact duplicate declarations from synthetic parent modules may coalesce;
- conflicting declarations should reject the multi-prefix merge and fall back
  to single-prefix or full source;
- import views are rebuilt through remapped symbols/modules;
- aliases preserve source order only within their original module path.

### Lowering

`CompiledLoweringSurface` references namespace symbols and sometimes runtime
source defs.

Rules:

- remap every value/type symbol through the namespace remap;
- keep path fields as diagnostic/debug guards;
- remap `source_def` only after runtime import remap is known;
- if a symbol or source def cannot be remapped, reject the multi-prefix merge.

### Typed

`CompiledTypedSurface` contains a compiled type arena plus value schemes.

Rules:

- each unit imports its compiled type arena into one merged type arena;
- remap value symbols through the namespace remap;
- remap every `Scheme` through a `CompiledTypeImporter`;
- do not share type variables by name across units;
- do not coalesce schemes by display text.

### Runtime

`CompiledRuntimeSurface::import_into` already imports one runtime surface into a
target arena and returns a `CompiledRuntimeImport`.

For merge:

- import each runtime surface into the same target arena;
- keep each unit's `CompiledRuntimeImport`;
- remap runtime `modules` and `values` through namespace remaps;
- preserve target arena roots in deterministic unit order;
- combine dump labels through the existing import path.

The merged runtime surface can be built from the target arena/labels plus
remapped module/value def records.

### Manifest

The merged manifest should represent the selected source-unit prefix set, not
the full source set.

Rules:

- files are the union of selected unit files, sorted by the original source file
  order;
- source hash is a new prefix-set cache key, not any individual unit key;
- surface hashes are recomputed from merged surfaces;
- errors are concatenated in deterministic unit order.

## Fallback Policy

Multi-prefix merge is an optimization. Any merge ambiguity should fall back
without changing program semantics.

Recommended order:

1. exact full-source poly/control cache;
2. exact full-source compiled-unit cache;
3. multi-prefix compiled-unit merge;
4. single-prefix source-unit cache;
5. full source compile.

Until the merge is stable, keep it behind a shadow assertion path:

- build with current single-prefix or full source path;
- also try multi-prefix merge;
- compare public poly dump or selected roots for small smoke cases;
- only switch the default after the shadow path is stable.

## First Implementation Slice

Start with a pure merge module, not CLI code:

```text
cache::merge_compiled_unit_artifacts(units: Vec<CachedCompiledUnitArtifact>)
    -> Result<CachedCompiledUnitArtifact, CompiledUnitMergeError>
```

Initial accepted cases:

- dependency-free units only;
- no overlapping non-root module paths except synthetic parents;
- value-only modules;
- no constructors, acts, roles, or methods.

Initial tests:

- two independent leaf modules merge and can be used as one prefix;
- conflicting same-path modules reject;
- act/constructor/role surfaces reject until remap coverage is implemented;
- fallback keeps CLI behavior unchanged when merge rejects.

Then expand coverage in this order:

1. syntax and namespace value/type remap;
2. typed value schemes;
3. runtime module/value def remap;
4. constructor payloads;
5. act operations and methods;
6. role shapes and role methods;
7. source-unit dependencies beyond dependency-free leaves.

## Implementation Status 2026-06-26

The pure merge path is now implemented for the source-unit prefix cases used by
the CLI:

- syntax surfaces merge by module path;
- namespace surfaces merge by module path and expose per-prefix module/value/type
  remaps;
- typed surfaces import schemes into one fresh compiled type arena;
- runtime surfaces import each unit into one fresh `poly::Arena` and expose
  per-prefix `DefId` remaps;
- lowering surfaces remap namespace symbols and runtime source defs;
- cache artifacts merge through `cache::merge_compiled_unit_artifacts`;
- the CLI tries a merged dependency-free source-unit prefix before falling back
  to the previous single-prefix source-unit path.

The accepted surface includes independent leaf modules and shared synthetic
parent modules. Shared parent `Def::Mod` nodes are coalesced by unioning their
children.

Dependency-bearing source units are now written as dependency-closure artifacts:
the artifact for unit `u` includes `u` plus all transitive dependency units in
one compiled unit. This keeps lowered runtime/lowering references inside the
same artifact and avoids serializing raw external `DefId`s.

The CLI selects cached prefix candidates by the source file set covered by each
artifact. Overlapping closure artifacts are not merged together; a larger
closure candidate wins, and uncovered files remain in the source suffix. This
keeps shared-dependency cases conservative while still allowing independent
closure artifacts to merge.

The first external-reference preparation is also in place:

- `BodyLoweringPrefix` records the imported runtime defs it brought into the
  prefix arena;
- the record keeps both the imported `DefId` set and path-bearing
  namespace-keyed module/value mappings;
- `lower_loaded_files_with_prefix` and `lower_root_loaded_file_with_prefix`
  carry that prefix runtime provenance into the combined `BodyLowering`.
- compiled-unit artifacts serialize that provenance as
  `CompiledUnitExternalRuntimeRefs`, including an `external_runtime_hash` in
  the manifest;
- compiled-unit merge remaps these external runtime refs through the same
  namespace/runtime remaps used by the merged surfaces.
- `CompiledRuntimeSurface::import_into_with_external_defs` can map selected
  source `DefId`s to already-imported target `DefId`s instead of fresh-copying
  them, and skips external roots / metadata during import.
- `compiled_unit_external_runtime_def_pairs` resolves serialized
  namespace-keyed external module/value refs against an already-imported prefix
  runtime by stable module/value path.
- `compiled_unit_complete_external_runtime_def_pairs` rejects artifacts whose
  reachable runtime graph still requires external `DefId`s not explained by
  those path-keyed refs. It intentionally does not require every prefix-owned
  `DefId` in the serialized table to be keyable, because skipped external
  bodies can contain private child defs that the suffix graph never imports.
- `CompiledRuntimeSurface::import_reachable_into_with_external_defs` imports
  only the non-external runtime graph reachable from local roots and metadata.
  This lets a dependent suffix reuse a dependency value def without copying the
  dependency body's private refs, patterns, or child defs.
- `BodyLoweringPrefix::extend_with_compiled_unit_surfaces_and_external_defs`
  can import a suffix compiled-unit surface on top of an existing prefix arena,
  preserving the dependency prefix's existing runtime defs.
- External-reference canaries now cover value refs, effect operations,
  constructors, type field methods, casts, role impl reuse, argument effect
  contracts, and root expressions. The source-unit smoke covers both
  independent merged prefixes and dependency-closure prefix hits.

This does not serialize dependent units without their dependencies yet. It only
gives the suffix lowering result a reliable way to distinguish prefix-owned
defs from defs created by the suffix, and persists that distinction in the
artifact. That is the prerequisite for turning dependency `DefId` references
into explicit external refs.

The remaining item is the more incremental external-reference design. A
dependent unit still cannot be serialized safely by lowering it against a
compiled dependency prefix and then dropping the dependency surfaces. Its
lowered body may contain `RefId` or metadata paths to dependency `DefId`s that
live in the prefix arena. If those external refs are left as raw arena-local
IDs, importing the artifact later will miswire or point at missing defs.

Therefore finer-grained dependency-bearing source-unit artifacts still need:

- cache selection that can import dependency artifacts first, then extend that
  prefix with a dependent artifact using the serialized external refs.
- a default route switch from dependency-closure artifacts to dependent-only
  artifacts after the external-reference import path has enough production
  coverage.

The closure artifact route is simpler and already implemented, but it can
duplicate dependency surfaces across related cached artifacts. The
external-reference table is still the route closer to realm/band incremental
compilation.

## Non-goals

- Do not use module path strings inside inference to decide types.
- Do not coalesce type variables across units by display name.
- Do not merge active solver graphs.
- Do not make public type projection read from cache-specific shortcuts.
- Do not make std a special case in the merge algorithm; std may become a
  large input, but the algorithm should be realm/band/source-unit based.

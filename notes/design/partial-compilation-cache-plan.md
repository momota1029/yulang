# Partial Compilation Cache Plan

This note is the working plan for moving Yulang from a process-local std clone
cache toward persistent file-SCC compiled artifacts.

The key correction is that the cache unit cannot be "std only" and cannot be
only serialized `CoreProgram`.

This plan uses the realm / band vocabulary from
`notes/design/source-realm-band-plan.md`:

- realm: versioned distribution boundary;
- band: import / namespace / build unit inside a realm.

Compiled-unit artifacts are still file-SCC artifacts. A realm or band is not
itself the compiled artifact unit; it provides identity and dependency context
for the SCC artifacts.

Yulang files contribute all of these to later files:

- operator syntax and parser tables;
- module namespace, values, types, reexports, and visibility;
- role, impl, effect, and method lookup tables;
- principal schemes and type evidence;
- runtime-facing core bindings.

Therefore the long-term cache unit is a source dependency SCC:

```text
SourceSet
  <- resolved SourceRealm / SourceBand identities
  -> source dependency graph
  -> SourceCompilationUnit SCC
  -> CompiledUnit artifact
```

`StdInferSnapshotData` and `StdCoreSnapshotData` remain useful prototypes. They
prove stable snapshot-local ids, serde payloads, and core serialization. They
are not the final architecture.

## Goals

- Make playground first run faster by avoiding repeated std/user dependency
  parsing, lowering, inference, and export where inputs have not changed.
- Keep user edits cheap by recompiling only affected file SCCs.
- Preserve syntax exports so downstream files can parse with cached operators.
- Preserve typed surfaces so downstream files can infer against cached schemes
  without re-lowering cached source.
- Preserve runtime surfaces so std/dependency core bindings can be merged into
  the user program without re-exporting cached dependencies.
- Keep cache invalidation explicit and conservative.

## Non-Goals

- Do not serialize a whole `LowerState` as the final format.
- Do not fake source-defined value/type defs without schemes and bodies.
- Do not make std a permanent special case.
- Do not cache debug-only evidence unless a downstream consumer requires it.
- Do not use stale artifacts if operator syntax, compiler version, feature
  flags, or dependency hashes differ.

## Existing Pieces

Current useful prototypes:

- `SourceSet::compilation_units()`
  - exposes file SCCs;
  - records unit dependencies;
  - records origin classification;
  - collects syntax exports per unit.
- `StdInferSnapshotData`
  - stable snapshot-local ids for modules, values, types, schemes, roles,
    effects, and effect operations.
- `import_std_infer_snapshot_data`
  - validates snapshot-local references;
  - partially maps snapshot ids back to builtin defs/modules;
  - reports missing paths structurally.
- `StdCoreSnapshotData`
  - serializable std `CoreProgram` prototype.
- `yulang-typed-ir` serde support
  - proves runtime-facing artifact serialization is viable.

## Compiled Unit Artifact

The target artifact should be split into layers. This keeps import order clear
and prevents core/runtime data from pretending to restore parser/lower state.

```rust
pub struct CompiledUnitArtifact {
    pub manifest: CompiledUnitManifest,
    pub syntax: CompiledSyntaxSurface,
    pub namespace: CompiledNamespaceSurface,
    pub typed: CompiledTypedSurface,
    pub runtime: CompiledRuntimeSurface,
}
```

### Manifest

The manifest decides cache validity.

Required fields:

- artifact format version;
- compiler snapshot version;
- resolved realm identity and version / revision;
- band path;
- unit id;
- unit origin;
- source files:
  - path;
  - module path;
  - source length;
  - source hash;
  - source origin;
- dependency unit hashes;
- relevant feature flags / environment knobs;
- parser/operator table format version;
- core IR format version.

The manifest should not include process-local `DefId`, `TypeVar`, `ModuleId`,
or `RefId`.

### Syntax Surface

Purpose: restore enough parser/operator information for downstream files before
they are parsed or re-parsed.

Required fields:

- public and our syntax exports from the unit;
- operator definitions by surface name;
- fixity/binding power data;
- exported/imported syntax dependency edges.

This layer is required because Yulang files can affect syntax through exported
operators. A core-only cache cannot parse downstream source safely.

Important operator split:

- Syntax surface owns parser-facing operator definitions:
  - surface operator name;
  - prefix/infix/suffix/nullfix availability;
  - binding power vectors;
  - visibility / reexport information relevant before parsing downstream
    files.
- Syntax surface does not own the lowered operator value identity. It should not
  contain process-local `DefId` or assume the operator body has been lowered.
- The serialized form should be independent of parser implementation details
  such as `SmallVec` layout. A small artifact type like
  `CompiledOperatorSyntax` should carry `Vec<i8>` binding powers and be
  convertible to/from parser `OpDef`.
- A cache hit for a dependency unit must be able to rebuild the downstream
  parser `OpTable` from syntax artifacts before parsing the downstream source.

### Namespace Surface

Purpose: restore names, modules, visibility, and canonical paths without
lowering source files again.

Required fields:

- module table entries;
- parent/child module edges;
- values and types with stable unit-local ids;
- operators mapped to value symbols;
- reexports;
- visibility;
- canonical value/type paths;
- builtin-backed symbols vs source-defined symbols.

Operator namespace identity belongs here, not in the syntax surface. Lowering
must resolve a parsed operator use through a stable imported mapping such as:

```text
(Infix) syntax token
  -> imported namespace entry (operator name + fixity)
  -> UnitValueId
  -> fresh process-local DefId
```

This separation is required because a single surface operator spelling can have
multiple fixities, and because parser syntax availability and lowered value
identity are consumed at different phases.

Import should allocate fresh process-local ids and build maps:

```text
UnitValueId -> DefId
UnitTypeId  -> DefId
UnitModuleId -> ModuleId
```

### Typed Surface

Purpose: let downstream inference use cached definitions as if the dependency
unit had been lowered and finalized.

Required fields:

- public/exported compact schemes;
- frozen schemes needed for generic instantiation;
- role declarations and role arg info;
- role methods and role method lookup by role;
- impl candidates and associated type data;
- effect declarations;
- effect methods;
- effect operations;
- relevant expected/principal evidence required by downstream export.

The typed surface must use unit-local ids and import through the namespace
surface maps.

### Runtime Surface

Purpose: provide runtime/exported code for cached dependency bindings.

Required fields:

- core bindings for exported/runtime-referenced dependency values;
- role impl member core bindings;
- effect operation runtime symbols;
- type graph/runtime graph view entries needed by downstream merge;
- principal evidence needed by runtime lowering/monomorphize.

This layer can reuse `CoreProgram`-style serde data, but it should be a unit
surface, not a standalone std program.

## Build Pipeline

The target build pipeline:

```text
collect sources
  -> parse leading metadata
  -> build dependency graph
  -> build SourceCompilationUnit SCCs
  -> for each unit in dependency order:
       if artifact valid:
         import syntax surface
         import namespace surface
         import typed surface
         import runtime surface
       else:
         parse/lower/infer/export unit
         emit artifact
  -> merge runtime surfaces for reachable units
  -> lower/monomorphize/vm
```

Important distinction:

- A cache hit imports surfaces.
- A cache miss compiles the unit and exports surfaces.
- The process-local lowered-std cache remains an oracle until compiled-unit
  import behaves the same.

## Runtime/Core Merge

Core artifacts need a merge step rather than replacing user export wholesale.

The merge must:

- include dependency core bindings before user root expressions;
- deduplicate by canonical path and artifact identity;
- reject conflicting bindings with the same path but different hashes;
- merge runtime symbols;
- merge principal evidence with id remapping where needed;
- avoid debug derived evidence in hot artifacts unless enabled.

This is the reason `StdCoreSnapshotData` is only a prototype: it serializes a
whole program, but the real cache needs mergeable unit surfaces.

## Implementation Phases

### Phase 0: Stabilize the Plan

Status: current.

- Keep `SourceSet::compilation_units()` as the source-layer boundary.
- Keep std snapshots as experiments only.
- Document the compiled-unit architecture in this note and reference it from
  `notes/todo.md` and `tasks/current.md`.

### Phase 1: Manifest and Syntax Surface

Build read-only artifacts from `SourceCompilationUnit`.

Tasks:

- Add `CompiledUnitManifest`.
- Add `CompiledSyntaxSurface`.
- Add a stable `CompiledOperatorSyntax` representation instead of serializing
  parser `OpDef` directly.
- Serialize direct and reexported syntax exports plus unit dependency hashes.
- Add an import helper that rebuilds an `OpTable` contribution from cached
  operator syntax.
- Add tests for:
  - operator exports in a cached unit;
  - reexported operator exports in a cached unit;
  - downstream parse using imported syntax surface;
  - `use ... without (...)` excluding cached operator syntax;
  - invalidation when operator source changes.

Success condition:

- A file depending on a cached operator-exporting unit can parse without
  re-reading that unit source.

### Phase 2: Namespace Surface

Tasks:

- Add `CompiledNamespaceSurface`.
- Serialize module/value/type/reexport/operator namespace entries.
- Represent operator values as `(operator name, fixity) -> UnitValueId`.
- Import namespace into fresh `LowerState` using fresh ids.
- Add stable local id maps.
- Add tests comparing:
  - normal lowering;
  - process-local cache lowering;
  - namespace-surface import + downstream lowering.
  - parsed cached operator uses resolving to the same canonical operator value
    as normal lowering.

Success condition:

- Downstream files can resolve cached module/value/type names without lowering
  dependency source.

### Phase 3: Typed Surface

Tasks:

- Serialize compact/frozen schemes for exported dependency values.
- Serialize role/impl/effect lookup data.
- Import typed surface into `Infer` / `LowerState`.
- Add collision-safe type-var remapping.
- Add tests for:
  - generic function imported from cached unit;
  - role method resolution through cached unit;
  - effect method lookup through cached unit.

Success condition:

- Downstream inference can typecheck against cached dependency schemes without
  lowering dependency bodies.

### Phase 4: Runtime Surface

Tasks:

- Convert `StdCoreSnapshotData` into `CompiledRuntimeSurface`.
- Make core bindings unit-local and mergeable.
- Add core evidence id remapping.
- Merge dependency runtime surfaces with user core export.
- Add tests for:
  - running a program whose dependency unit is imported from runtime surface;
  - role impl member body from cached unit;
  - effect handler helper from cached unit.

Success condition:

- A cached dependency unit can be skipped during infer/export and still execute.

### Phase 5: Persistent Wasm Bundle

Tasks:

- Build std compiled-unit artifacts at wasm package build time.
- Embed artifacts as bytes.
- On startup, import syntax/namespace/typed/runtime surfaces.
- Fall back to source std compile if manifest validation fails.
- Expose cache status in console timings.

Success condition:

- First playground run avoids std lowering/export on cache hit.

### Phase 6: General User Dependency Cache

Tasks:

- Store artifacts in CLI cache dir or browser IndexedDB/local storage.
- Cache user dependency SCCs by source hash and dependency hash.
- Recompile only invalidated SCCs.

Success condition:

- Editing the entry file does not recompile unchanged user dependencies.

## Invalidation Rules

Invalidate a unit if any of these differ:

- artifact format version;
- compiler version/snapshot version;
- parser/operator table version;
- feature flags affecting parse/lower/infer/export;
- source hash or source length;
- module path;
- dependency unit hash;
- std/prelude implicit import behavior;
- public syntax exports.

When in doubt, miss the cache.

## Safety Rules

- A partial import must never claim it can replace lowering.
- Missing value/type bodies are import gaps, not fake defs.
- Core/runtime merge must reject conflicting canonical paths.
- Operator syntax must be restored before parsing dependent source.
- Debug evidence should stay opt-in.
- The process-local cache remains the behavioral oracle until full compiled-unit
  import matches it.

## Near-Term Next Step

Build the first `CompiledUnitManifest + CompiledSyntaxSurface` from
`SourceCompilationUnit`.

This is intentionally before typed/runtime import. It fixes the biggest design
hole in the std snapshot prototype: syntax exports and file-SCC identity.

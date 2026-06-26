# Realm Cache Strategy

Date: 2026-06-26

This note records the cache split to use while implementing realm / band
resolution. The goal is to avoid turning `realm.toml` back into a package
summary, while still making ordinary file runs and future realm imports fast.

## Options

### Realm Owns A Cache From The Beginning

A realm should define the cache namespace, but it should not store mutable
compiler artifacts inside the source realm by default.

Reasons:

- A realm may be read-only: embedded std, downloaded snapshots, git checkouts,
  browser bundles, and registry archives should all be usable without writes.
- Source collection currently runs before artifact cache lookup. Keeping that
  invariant prevents stale cache entries from changing which files are loaded.
- `realm.toml` is intentionally not a dependency/version summary. A hidden
  mutable realm-local build cache would reintroduce a package-level state
  surface through another route.

Accepted shape:

```text
persistent user cache
  /realms/<resolved-realm-key>/resolution/
  /artifacts/<stage>/<artifact-key>
```

Project-local `target/yulang` may mirror this later for developer ergonomics,
but the semantic cache identity is still derived from resolved realm identity,
band path, source hashes, and dependency interface hashes.

### Split Artifact Cache By Realm Resolution

This is the safe next step.

The source text request is not enough for artifact identity:

```yulang
use ui/widget::a v2 with program::ui
```

The same source-site request may resolve to different exact realms over time or
under a different lock. The cache key must therefore include structured
resolution metadata, and later the exact resolved target:

```text
source file hash
source-site request path/version/with
resolved realm identity
resolved revision/version
resolved source digest
band path
public dependency/interface hash
```

Current implementation status:

- `UseImport` preserves route, version-family suffix, and `with` anchor.
- `CollectedSource` carries resolution imports.
- source and source-unit cache keys hash those imports.

Next implementation step:

- add a persistent resolution-entry cache that maps source-site requests to
  exact local realm/band targets;
- once exact target identity is available, hash it in addition to the request;
- teach source-unit dependency analysis that cross-band imports create
  dependency edges distinct from `mod` containment edges.

### Accumulate Generated Mono In The Realm Cache

Do not make mono a realm-owned cache artifact yet.

Mono is not only a property of a realm snapshot. It depends on:

- the typed public/internal surfaces imported into the current program;
- demand-specialization roots;
- specialization options and compiler schema;
- host/runtime backend choices;
- future realm/band dependency interface hashes.

Safe future shape:

```text
typed / runtime compiled-unit surface
  -> specialization demand key
     -> mono artifact
        -> backend artifact
```

The realm cache can index mono artifacts by resolved realm and band for lookup
convenience, but the validity key must be the typed/runtime surface plus demand
configuration. It should not be keyed only by realm version.

## Implementation Order

1. Preserve source-site resolution metadata and include it in source cache keys.
2. Persist exact resolution entries for local realm/band targets.
3. Add resolved cross-band dependency edges to source-unit cache planning.
4. Add realm-scoped cache directories as a namespace for resolution entries.
5. Only after typed/runtime surface keys are stable, prototype mono artifacts.

This order keeps cache lookup behind source collection and avoids using cache
state to decide what source files exist.

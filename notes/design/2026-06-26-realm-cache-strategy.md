# Realm Cache Strategy

Date: 2026-06-26

This note records the cache split used while realm / band resolution is being
implemented. The main constraint is that cache state must not turn
`realm.toml` back into a package summary or decide which source files exist.

## Decisions

### Source Realms Are Cache Namespaces, Not Mutable Build Directories

A realm may be read-only: embedded std, downloaded snapshots, git checkouts,
browser bundles, and registry archives should all work without writes.

Therefore compiler artifacts live in the persistent user cache:

```text
user cache
  artifacts/
    compiled-unit/
    poly/
    mono/
    control-vm/
  realms/<source-realm-key>/
    resolution/
```

Project-local `target/yulang` may mirror this later for developer ergonomics,
but the semantic cache identity still comes from source hashes, resolved realm
identity, band path, dependency interface hashes, and compiler cache schema.

### Source Collection Remains The Authority

Cache lookup must not silently change local source selection.

For local current-realm bands, the resolver has a deterministic candidate:

```text
realm/foo::bar  ->  <current realm root>/foo.yu
```

The resolution cache may accelerate or validate this path, but it cannot
redirect to another file. If the cached target path differs from the
deterministic candidate, source collection ignores the cache and falls back to
normal filesystem resolution.

This rule is stricter than what future global providers will need, but it keeps
the first local implementation safe.

### Resolution Entries Are Per Source Site

The surface request alone is not enough:

```yulang
use ui/widget::a v2 with program::ui
```

The same source-site request can resolve differently under a different lock,
provider, or source tree. Cache keys therefore include the source-site context
and structured request metadata:

```text
source file path/module/source
request path
request route
version-family suffix
with anchor
compiler cache schema
```

For global providers, the exact resolved target should also be reflected before
compiled artifacts are shared across source sets.

### Mono Is Exact Source/Resolution Keyed For Now

Mono is not only a property of a realm snapshot. It depends on:

- typed public/internal surfaces imported into the current program;
- demand-specialization roots;
- specialization options and compiler schema;
- host/runtime backend choices;
- future realm/band dependency interface hashes.

The safe near-term cache chain is:

```text
source / resolution exact key
  -> poly artifact
  -> mono artifact
  -> control artifact
```

The realm cache may later index mono by resolved realm/band for lookup
convenience, but validity must be keyed by typed/runtime surface plus
specialization demand. Do not reuse mono across different source sets merely
because they mention the same realm snapshot.

### Release Snapshots Publish `.yucu`, Not Exact Program Caches

Future release/freeze commands should treat `.yucu` as the only compiled cache
artifact that belongs in a realm/band release snapshot.

```text
released realm/band snapshot
  -> source files
  -> exact resolution metadata
  -> compiled-unit `.yucu` artifacts for published band roots
```

`.yucu` is the dependency-prefix artifact. It stores syntax, namespace, typed,
and runtime surfaces that another program can import without rerunning the
whole dependency through lowering and inference. It is still a cache: the
release source snapshot remains authoritative, and stale or missing `.yucu`
entries can be rebuilt from that fixed source snapshot.

Do not include `.yuir`, `.yumo`, or `.yuvm` in the default release snapshot.
Those artifacts are exact source-set / exact program caches and should stay
local to the command that produced them.

## Implemented

### Resolution Metadata

- `UseImport` preserves route, version-family suffix, and `with` anchor.
- `CollectedSource` carries `resolution_imports`.
- full-source and source-unit cache keys hash those structured imports.

### Persistent Resolution Cache

Resolution entries are stored under:

```text
realms/<source-realm-key>/resolution/<request-key>.yures
```

A `.yures` entry stores:

- source realm identity;
- original structured request;
- target realm identity;
- target band path;
- target module path;
- target source path;
- target source length and source hash.

Cached CLI builds populate current-realm entries after source collection. This
is a recording step; the collector has already found the source files.

### Checked Current-Realm Lookup

Cached CLI source collection can use current-realm entries as checked lookups.
The lookup is accepted only when all of these hold:

- source realm in the entry matches the current source realm;
- target realm in the entry matches the current source realm;
- target band and module path match the requested band root;
- cached path canonicalizes to the deterministic `<realm>/<band>.yu` path;
- current file contents match the cached target source length/hash.

If any check fails, collection falls back to `resolve_realm_band_file`.

This means stale, corrupted, or redirected `.yures` entries cannot change local
source selection.

### Source-Unit Dependency Planning

Route-aware resolution imports are included in source-unit dependency planning:

- `realm/...::...` imports depend on the loaded current-realm band root;
- `band::...` imports depend on the longest loaded module prefix in the current
  band;
- slash-qualified cross-realm imports do not guess a local dependency edge
  until the future global resolver loads or rejects them.

### Exact Mono Artifact

Exact source/resolution-keyed mono artifacts are stored under:

```text
artifacts/mono/<source-key>.yumo
```

The CLI reads/writes `.yumo` after the poly stage in:

- `dump-mono`;
- `run-mono`;
- cached control builds when the exact control artifact did not hit.

`yulang cache stats` reports the `mono` artifact count.

## Not Implemented Yet

- slash-qualified global realm provider resolution;
- `with` anchor solving against public dependency/reexport surfaces;
- exact lock projection for source-site requests;
- resolved target identity in the full source artifact key beyond the
  structured source-site metadata already stored in `CollectedSource`;
- realm-indexed mono sharing by typed/runtime surface plus specialization
  demand;
- use of `.yures` to choose non-local provider files.
- release/freeze command support for materializing `.yucu` artifacts alongside
  fixed source snapshots.

## Guardrails

Do not add these shortcuts:

- do not write mutable compiler artifacts into the source realm by default;
- do not add human-written dependency versions to `realm.toml`;
- do not let a local `.yures` entry redirect `realm/foo::...` away from
  `<current realm>/foo.yu`;
- do not treat `.yumo` as a realm-level mono cache;
- do not merge cross-realm source-unit dependencies by path string before the
  resolver has produced an exact structured target.

## Next Steps

1. Define slash-qualified provider records in `realm.toml` without adding
   realm-wide dependency requests.
2. Add a global resolver that produces exact target identity and source
   fingerprint before source collection imports the file.
3. Project exact per-source-site resolutions into a lock file or diagnostic
   view.
4. Extend artifact keys with resolved target identity where source-site
   metadata alone is not enough.
5. Prototype typed/runtime-surface-keyed mono sharing only after specialization
   demand can be represented explicitly.

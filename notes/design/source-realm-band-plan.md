# Source Realm / Band Plan

This note defines the source-level packaging vocabulary for Yulang.

The design intentionally follows the Go module/package shape more than the Rust
crate/module shape, but uses Yulang words:

```text
registry / host
  -> realm
     -> band
        -> source file
```

## Terms

### Registry / Host

A registry or host is where realms are found.

Examples:

- `github.com`
- a private git host;
- a local filesystem root;
- an embedded std source bundle;
- a future Yulang registry.

The registry is not a compilation unit and is not part of normal source
identity except through the realm identity it resolves.

### Realm

A realm is the versioned distribution boundary.

Examples:

```text
github.com/momota1029/yulang-extra@v0.1.0
file:///home/me/lib
embedded:std@2026.05
```

A realm owns:

- identity;
- optional version or revision;
- root source tree or archive;
- dependency requirements;
- a resolved dependency lock when reproducible builds require it;
- zero or more bands;
- cache identity for source and native artifacts.

The important rule is:

```text
realm versions are fixed when the realm is published.
bands do not have independent versions.
```

Therefore a band identity is always:

```text
resolved realm identity + band path
```

### Band

A band is the import / namespace / build unit inside a realm.

It is closest to a Go package. It is intentionally shorter than `package` and
fits Yulang's `pub` / `our` vocabulary: a band is the group that shares `our`
definitions and exports `pub` definitions.

A band owns:

- band path inside its realm;
- source files;
- public and our exported names;
- syntax exports;
- file dependency SCCs;
- compiled-unit artifacts for its SCCs.

Bands are not published independently. If `tools@v1.2.0` contains `cli` and
`parser`, both are part of the same `tools@v1.2.0` snapshot:

```text
tools@v1.2.0:cli
tools@v1.2.0:parser
```

### Band Boundary

The near-term source boundary is defined by `mod`, not by a new manifest file.

`mod child` is same-band inclusion. It may resolve only to:

- `child.yu` next to the current source file;
- `current_file_stem/child.yu`.

It does not walk upward and it does not read `child/mod.yu`. This keeps `mod`
as a local tree edge. A file that is not reached through a `mod` edge becomes a
band root. In other words, a band is the source subtree that cannot be climbed
past by more `mod` edges.

This gives two important future hooks:

- `band::name` can mean an absolute path from the current band root.
- `use realm/...` or `our use realm/...` can import another resolved realm /
  band without pretending it is a local `mod`.

`mod` and band/realm imports are therefore separate operations. `mod` grows the
current band. `use` can depend on another band once realm resolution exists.

## Dependency Rules

Same-realm imports use the same resolved realm snapshot:

```text
tools@v1.2.0:cli
  -> tools@v1.2.0:parser
```

Cross-realm imports use the version selected by the importing realm's manifest
and lock:

```text
app@v2.0.0:main
  -> tools@v1.2.0:parser
```

The compiler should avoid allowing a band inside `tools@v1.2.0` to depend on
`tools@v1.1.0:parser` as if it were a normal same-realm import. That makes
same-realm identity ambiguous and complicates cache keys.

## Import Path Split

An external import path is resolved in three parts:

```text
use github.com/user/tools/parser

host:  github.com
realm: github.com/user/tools
band:  parser
```

The version is normally not written in source. It is selected by a realm
manifest and lock:

```text
require github.com/user/tools v1.2.0
```

## Relation To Existing SourceSet

`SourceSet` remains the collected source graph for one compilation.

The new vocabulary is layered above it:

```text
SourceRealm
  -> SourceBand
     -> source files

SourceSet
  = files collected for one compile from one or more resolved bands

SourceCompilationUnit
  = file dependency SCC inside a SourceSet / SourceBand graph

CompiledUnitArtifact
  = persistent artifact for a SourceCompilationUnit
```

Do not turn `SourceSet` into a realm or band. `SourceSet` is a build input
aggregate; `realm` and `band` are source identity concepts.

## Cache Keys

Compiled artifacts should eventually include:

- compiler version;
- artifact format version;
- resolved realm identity;
- resolved realm version / revision;
- band path;
- source file identities;
- dependency band/unit hashes;
- feature flags and relevant environment knobs.

The cache should never rely on a band path alone. A band path becomes meaningful
only after its realm has been resolved.

## Cache Locations

Yulang uses three storage classes.

Project-local build output:

```text
target/yulang/
  bin/
  obj/
  build/
  dump/
```

This is for generated output tied to the current checkout:

- final native executable experiments in `bin/`;
- project-local object files in `obj/`;
- link / compile scratch directories in `build/`;
- control IR / CPS IR / ABI IR dumps;
- temporary debug artifacts;
- anything that may disappear with project build output.

CLI native output flags use these locations when the output path is omitted:

```text
--native-object     -> target/yulang/obj/<entry>.o
--native-exe        -> target/yulang/bin/<entry>
--native-value-exe  -> target/yulang/bin/<entry>-value
--native-run-exe    -> target/yulang/bin/<entry>, then run it
--native-run-value-exe
                    -> target/yulang/bin/<entry>-value, then run it
```

Explicit output paths still win.

Persistent user cache:

```text
$YULANG_CACHE_DIR/
$XDG_CACHE_HOME/yulang/
~/.cache/yulang/
```

This is for reusable cache entries:

```text
realms/
compiled-units/
native/
```

The default resolver prefers `YULANG_CACHE_DIR`, then `XDG_CACHE_HOME/yulang`,
then `~/.cache/yulang`. If none of those are available, it falls back to a temp
directory and treats the cache as disposable.

Project identity files:

```text
realm.toml
yulang.lock
```

`realm.toml` declares the current realm. `yulang.lock` records resolved realm
dependencies and revisions. The lock file is not a cache; it is part of
reproducible source identity. Fetched realm contents and compiled artifacts
live in the persistent user cache.

## Initial Implementation Shape

Start with small identity types in `yulang-source`:

```rust
SourceRealm
ResolvedRealmId
RealmIdentity
RealmVersion
SourceBand
BandPath
ResolvedBandId
```

These types should be data boundaries first. They should not force source
loading, dependency fetching, or compiled artifact caching to be rewritten in
one step.

Current first slice:

- `SourceSet` carries resolved `SourceRealm` values.
- Each `SourceFile` may point at a `ResolvedBandId`.
- `YulangCachePaths` defines the stable path split:
  `target/yulang`, persistent user cache directories, `realm.toml`, and
  `yulang.lock`.
- `CompiledUnitArtifactCache` can write and read full compiled-unit artifacts
  under `compiled-units/v<artifact-format>/parser-v<parser-format>/`.
  It validates artifact / parser format versions and rejects mismatched
  manifest keys on read.
- virtual source loading creates a `virtual:entry` realm with one root band.
- local file loading creates a `file://...` realm rooted at the entry file's
  directory.
- files connected by `mod` edges share a band.
- files loaded only through `use` start separate bands in the same realm for
  now.
- inline source loading creates an `embedded:inline` realm and assigns bands by
  the same `mod` edge rule.

This is intentionally still mostly an identity and storage layer. It does not
yet read a realm manifest, fetch git dependencies, resolve `use realm/...`,
implement `band::` absolute lookup, or automatically use the persistent
compiled-unit cache during lowering.

Resolver work can then proceed in phases:

1. local realm and virtual single-file realm;
2. local bands from `mod` edges;
3. `band::` absolute lookup from the current band root;
4. realm manifest and lock file;
5. `use realm/...` resolution;
6. git / GitHub realm fetch;
7. persistent realm fetch cache;
8. compiled artifact cache lookup / invalidation in the source lowering
   pipeline;
9. browser embedded realms and IndexedDB/local storage cache.

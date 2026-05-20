# Source Realm / Band Plan

This note defines the source-level packaging vocabulary for Yulang.

The current target shape is:

```text
registry / host
  -> realm@version
     -> band
        -> module tree
           -> source file
```

The public identity is intentionally close to Yulang / Rust namespace syntax:

```text
yulang@0.1.3/std::prelude
```

This means:

```text
realm:      yulang@0.1.3
band:       std
module:     prelude
```

`/` separates the resolved realm from the band. `::` stays inside the band and
is also the normal module / value / type path separator. A version belongs to
the realm, never to a band.

## Design Summary

- A realm is the versioned source universe / distribution boundary.
- A band is the crate-like import, namespace, and build boundary inside a
  realm.
- A module tree lives inside one band and is grown by `mod`.
- Bands do not have independent versions.
- A band identity is `resolved realm identity + band path`.
- Compiled artifacts are still source-dependency SCC artifacts. Realm and band
  identity provide context for those artifacts; they are not necessarily the
  final cache unit by themselves.

The intended cache hierarchy is:

```text
SourceRealm
  -> SourceBand
     -> SourceDependencyScc
        -> CompiledUnitArtifact
```

## Surface Identity

The canonical external form is:

```text
realm@version/band::module::item
```

Examples:

```text
yulang@0.1.3/std::prelude
github.com/user/app@1.2.0/main
github.com/user/ui@2.0.1/widget::button
```

The parser may accept a surface version suffix such as a trailing `v1.2`
because the CST already has that shape. Lowering should extract that suffix as
structured version metadata and canonicalize it before resolution:

```text
surface:   github.com/user/ui/widget::button v1.2
canonical: github.com/user/ui@1.2/widget::button
```

Grouped imports may put the suffix on each item, or once after the group as a
default for unversioned items:

```yulang
use user/{realm1 v1.3, realm2::a::b::c v1.4}
use realm/band::{module1, module2::*} v1.2
```

Rules:

- at most one version spec may appear in a realm reference;
- the version spec belongs to the realm;
- the version spec is not a path segment;
- cache keys use canonical resolved identity, not the original CST text.

If the surface form is ambiguous, the resolver should report a path/version
diagnostic instead of guessing a band split.

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
yulang@0.1.3
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

It is closest to a Rust crate in how Yulang code should feel, while keeping the
Go-like idea that one versioned distribution can contain several independently
importable units. A band is the group that shares `our` definitions and exports
`pub` definitions.

A band owns:

- band path inside its realm;
- source files in its module tree;
- public and our exported names;
- syntax exports;
- file dependency SCCs;
- compiled-unit artifacts for its SCCs.

Bands are not published independently. If `yulang@0.1.3` contains `std` and
`ui`, both are part of the same `yulang@0.1.3` snapshot:

```text
yulang@0.1.3/std
yulang@0.1.3/ui
```

Inside the same resolved realm, a path such as `std::prelude` starts at the
`std` band and then enters the `prelude` module within that band.

### Module

A module is a path segment inside one band.

Modules are grown by `mod`, not by package metadata. The compiler should keep
this split explicit:

```text
RealmId / BandId :: ModulePath
```

That split is important because `std::prelude::Display` means:

```text
band:   std
module: prelude
item:   Display
```

It does not mean that `std::prelude` is a nested band.

## Band Boundary

The near-term source boundary is defined by `mod`, not by a new manifest file.

`mod child` is same-band inclusion. It may resolve only to:

- `child.yu` next to the current source file;
- `current_file_stem/child.yu`.

It does not walk upward and it does not read `child/mod.yu`. This keeps `mod`
as a local tree edge.

A file that is not reached through a parent `mod` edge becomes a band root. In
other words, a band is the source tree whose parent is not another local module
inside the same band.

Example:

```text
realm yulang@0.1.3
  band std
    mod prelude
    mod list
    mod ops
  band ui
    mod widget
```

This makes these paths natural:

```text
std::prelude
std::list
ui::widget
```

It also makes `pub use ui::widget` a same-realm reexport from one band to
another, as long as visibility allows it.

`mod` and band / realm imports are therefore separate operations. `mod` grows
the current band. `use` can depend on another band once realm resolution exists.

## Import And Use Resolution

### Same-Realm Lookup

Same-realm imports use the same resolved realm snapshot:

```text
yulang@0.1.3/std::prelude
  -> yulang@0.1.3/ui::widget
```

The compiler should avoid allowing a band inside `yulang@0.1.3` to depend on
`yulang@0.1.2/std` as if it were a normal same-realm import. That makes
same-realm identity ambiguous and complicates cache keys.

### Cross-Realm Lookup

Cross-realm imports use the version selected by the importing realm's resolver
state and lock:

```text
github.com/user/app@2.0.0/main
  -> github.com/user/ui@1.2.0/widget::button
```

The source path may omit the version if the realm resolver can choose it from a
lock file, a previous import, or a `with` constraint. After resolution, the
compiler should work only with the resolved canonical identity.

### `with` Version Alignment

`with` is a version alignment constraint. It is not an import by itself.

Example intent:

```text
use user/program
use ui/widget::a with program
```

The first import resolves the `program` band from the `user` realm. The second
import targets the `widget` band from the `ui` realm and asks the resolver to
use the same `ui` realm version that the already resolved `program` dependency
exposes. This works only when `program` publicly exposes a matching dependency
or reexport such as `program::ui`. Private implementation dependencies of
`program` are not visible to `with`.

Resolver rule:

```text
target import + with anchor
  -> read the anchor's public dependency / reexport surface
  -> find the target realm identity
  -> reuse the anchor-selected version
```

If the target import also requests a different explicit version, the resolver
should report a conflict:

```text
use ui/widget with program     # program exposes ui@1.2.0
use ui/widget v2.0 with program
                               # conflict: explicit ui@2.0 vs anchored ui@1.2
```

`with` participates in lock resolution and cache identity because it changes the
resolved realm version even when the target source path is the same.

## Relation To Go And Rust

The design borrows Go's useful split:

```text
module version
  -> many packages/import units
```

Yulang names the versioned module-like boundary `realm`, and the import unit
`band`.

The surface syntax is deliberately not Go-like. Go lets directory paths under a
module become package paths. Yulang should keep a clearer split:

```text
realm@version/band::module
```

This keeps standard library paths such as `yulang@0.1.3/std::prelude` close to
the existing Rust/Yulang namespace feel while still supporting URL-like realm
resolution.

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
- parser / operator table format version;
- resolved realm identity;
- resolved realm version / revision;
- band path;
- source dependency SCC identity;
- source file identities;
- source hashes and syntax export hashes;
- dependency band interface hashes;
- dependency SCC artifact hashes;
- feature flags and relevant environment knobs.

The cache should never rely on a band path alone. A band path becomes meaningful
only after its realm has been resolved.

Downstream invalidation should primarily flow through public interface hashes:

```text
dependency source SCC changed
  -> dependency band public interface hash changed
  -> downstream cache entries invalidated
```

Internal SCC artifacts may change without invalidating downstream bands when
the exported syntax / namespace / typed / runtime surfaces remain compatible.

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

`realm.toml` declares the current realm when a project wants explicit realm
identity. It is not required to declare bands. `yulang.lock` records resolved
realm dependencies and revisions. The lock file is not a cache; it is part of
reproducible source identity. Fetched realm contents and compiled artifacts
live in the persistent user cache.

## Initial Implementation Shape

Start with small identity types in `yulang-sources`:

```rust
SourceRealm
ResolvedRealmId
RealmIdentity
RealmVersion
SourceBand
BandPath
ResolvedBandId
ModulePath
ResolvedSourcePath
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
- `use mod path::*` is parsed as `mod path; use path::*` sugar at source
  metadata level, so small local realm/band examples do not need a separate
  leading `mod` declaration.
- `use ... with anchor` is parsed and preserved on `UseImport` metadata. The
  current lowerer ignores the suffix for ordinary import binding, so the syntax
  can be introduced before cross-realm version resolution is implemented.
- `YulangLockFile` defines a serializable first lock schema for resolved realms,
  realm dependencies, and `with` alignment constraints.
- `collect_source_with_constraints` gathers `use ... with ...` source metadata
  into structured constraints, `YulangLockFile::from_source_set` can project the
  current `SourceSet` into a lock-shaped value, and lock validation rejects
  conflicting resolved realms for the same target/anchor pair.
- local source collection reads `realm.toml` when present. The current schema
  supports `[realm] identity/version` and `[dependencies]`, and uses that data
  for `SourceRealm` identity plus lock dependencies.
- `parse_canonical_realm_path` parses the canonical
  `realm@version/band::module` shape into realm identity/version, band path, and
  module path. It keeps slashes before the final `/` inside the realm identity,
  so `user/program@2.0/ui::widget` resolves as realm `user/program`.
- `use realm/band::module v1.2` parses the trailing `v...` suffix as source
  metadata (`realm_version`) without adding it to the normal import path. A
  suffix on a grouped item wins over an outer group suffix; the outer suffix
  fills only imports without an item suffix. The ordinary lowerer ignores the
  suffix, while lock constraint collection can preserve it as the resolved
  realm version.
- `yulang lock <path>` writes the current lock-shaped source graph to
  `yulang.lock` (or `--out PATH`). `yulang lock <path> --check` reads the lock
  file, validates its `with` constraints, and fails if the generated graph would
  change it.
- files loaded only through `use` start separate bands in the same realm for
  now.
- inline source loading creates an `embedded:inline` realm and assigns bands by
  the same `mod` edge rule.

This is intentionally still mostly an identity and storage layer. It does not
yet fetch git dependencies, resolve external realm imports, implement full
`band::module` absolute lookup, resolve `with` constraints, or automatically
use the persistent compiled-unit cache during lowering.

Resolver work can then proceed in phases:

1. local realm and virtual single-file realm;
2. local bands from `mod` edges;
3. `band::module` absolute lookup from the current realm;
4. canonical path parser for `realm@version/band::module`;
5. version suffix extraction from CST into structured resolver metadata;
6. realm manifest and lock file;
7. cross-realm `use` resolution;
8. `with` version alignment constraints;
9. git / GitHub realm fetch;
10. persistent realm fetch cache;
11. compiled artifact cache lookup / invalidation in the source lowering
    pipeline;
12. browser embedded realms and IndexedDB/local storage cache.

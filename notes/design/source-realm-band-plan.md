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

## Current Decisions

- A realm is the versioned distribution and snapshot boundary.
- A band is the import / namespace / build boundary inside one realm.
- A module tree lives inside one band and is grown by `mod`.
- A resolved realm snapshot is described by three separate graphs:
  - `G_mod`: structural source containment created by `mod`;
  - `G_source`: semantic source dependencies inside a band;
  - `G_band`: cross-band imports and reexports.
- `G_mod` must be a forest. Each source has at most one `mod` parent, each tree
  has exactly one root, and each tree defines one band.
- `G_source` may contain cycles. Its SCCs are compilation and cache units.
- `G_band` must be acyclic. Cross-band cycles are rejected.
- A bare `foo::bar` path never crosses a band boundary.
- Current-band absolute paths use the reserved `band` qualifier:

```text
band::path::to::func
```

- Same-realm cross-band imports use the reserved current-realm qualifier:

```text
realm/foo::bar
realm/path/to/band::foo::bar
```

- `std::...` is a prebound alias, not a generic band fallback rule.
- All unowned `.yu` source roots in a realm snapshot are band roots in the
  first design.
- If two versions from the same realm family are imported into one local scope,
  an explicit alias is required:

```yulang
use theme/colors as theme1 v2
```

- A source-level suffix such as `v2` is a version-family request. The lock
  records the resolved exact version or revision.
- `with` can align only against public dependency / reexport surfaces.
  Private dependencies are not alignment anchors.
- `realm.toml` must not contain human-written versions. It may declare the
  current realm identity and source providers, but dependency requests live at
  each `use` site and exact resolutions are cached per source file.
  `snapshot.json` / `yulang.lock` record those resolutions for reproducible
  realms and human-facing review.
- Repository source providers should be specified in git-oriented terms before
  implementation: provider name and repository locator in `realm.toml`, plus
  resolved commit, source digest, and diagnostics in `yulang.lock`.

## Design Summary

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

The parser accepts a surface version suffix such as a trailing `v1.2` because
the CST already has that shape. Lowering should extract that suffix as
structured version-family metadata and canonicalize it before resolution:

```text
surface:          github.com/user/ui/widget::button v1.2
resolver request: github.com/user/ui with version family v1.2,
                  band widget, module button
```

After lock resolution, the canonical identity contains the exact resolved
version or revision. The surface suffix is not itself the resolved identity.

Same-realm cross-band imports use `realm/` as an explicit current-realm
qualifier:

```text
realm/ui::widget
realm/ui::widget::button
realm/tools/parser::json::value
realm/path/to/band::foo::bar
```

Current-band absolute paths use the reserved `band` qualifier:

```text
band::path::to::func
```

Bare paths stay inside the current band:

```text
foo::bar
```

This never falls back to a same-realm band named `foo`.

The separator rule is:

```text
before the band boundary: /
inside the band:          ::
```

`std::foo` follows this rule because `std` is a prebound alias that already
resolves to a band.

Grouped imports may put the suffix on each item, or once after the group as a
default for unversioned items:

```yulang
use user/{realm1 v1.3, realm2::a::b::c v1.4}
use user/theme/colors as theme1 v2
use user/theme/{colors as theme1 v2, fonts as theme_fonts v2}
```

Rules:

- at most one version spec may appear in a realm reference;
- the version spec belongs to the realm;
- the version spec is not a path segment;
- an alias appears before the version suffix when both are present:
  `use theme/colors as theme1 v2`;
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
- optional source provider declarations;
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

Physical storage is not canonical identity. A local project may freeze editable
source under `.yulang/versions/<version>/`, while a repository/cache layout may
store snapshots under a realm-owned `@v` directory such as:

```text
std/@v/0.1.0/...
```

If that snapshot contains a root `realm.yu`, the single-band case can be laid
out as `realm = band` without introducing an empty default band.

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

Inside the same resolved realm, ordinary bare paths stay inside the current
band. Cross-band access uses the reserved current-realm qualifier:

```text
realm/ui::widget
```

The familiar `std::prelude` shape is provided by a prebound alias for the
standard library. It is not a generic rule that a bare first segment may become
a same-realm band.

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

That reading happens after the prebound `std` alias has resolved. It does not
mean that every bare `foo::bar` path can discover a same-realm band named
`foo`, and it does not mean that `std::prelude` is a nested band.

## Band Boundary

The near-term source boundary is defined by `mod`, not by a new manifest file.

`mod child` is same-band inclusion. It may resolve only to:

- `child.yu` next to the current source file;
- `current_file_stem/child.yu`.

It does not walk upward and it does not read `child/mod.yu`. This keeps `mod`
as a local tree edge.

For each resolved realm snapshot, the compiler first builds a structural
`G_mod` graph. This graph must be a forest:

- no `mod` containment cycles;
- each source file has at most one parent `mod` edge;
- each weak component has exactly one root;
- that root defines the band;
- every unowned `.yu` source root in the realm snapshot becomes an importable
  band root.

The compiler should reject structural ambiguity instead of picking precedence:

- one source claimed by multiple module parents;
- a `mod` cycle;
- two physical candidates for one `mod child`;
- logical source paths that differ only by case or symlink identity;
- a source first used as a band root but later discovered to be owned by a
  different band's `mod` tree.

After this pass, the realm has a `BandIndex`:

```text
BandPath -> root SourceId
SourceId -> owning BandId + ModulePath
```

Ordinary `use` resolution should read this index instead of discovering bands
on demand. Discovery order must not change source identity.

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

This makes these canonical paths natural:

```text
yulang@0.1.3/std::prelude
yulang@0.1.3/std::list
yulang@0.1.3/ui::widget
```

In source, same-realm cross-band access uses `realm/`:

```yulang
pub use realm/ui::widget
```

This is a same-realm reexport from one band to another, as long as visibility
allows it.

`mod` and band / realm imports are therefore separate operations. `mod` grows
the current band. `use` can depend on another band once realm resolution exists.

## Import And Use Resolution

### Manifest, Requests, Resolution Cache, And Lock

`realm.toml` is not a package-summary dependency graph. In particular, humans
should not write versions there. Doing so would force the whole realm to agree
on one package-level version choice and would block file-level imports from
resolving different variables of the same realm family.

Keep the responsibilities separate:

```text
realm.toml
  -> declares the current realm identity and optional source providers

use ... vN / use ... with anchor
  -> declares a local dependency request at the source site

per-file resolution cache
  -> maps source-site requests to exact resolved snapshot / commit / digest

yulang.lock
  -> records and constrains observed exact resolutions for reproducible realms
```

This means a source file may choose its own realm-family request:

```yulang
use theme/colors as theme1 v1
use theme/colors as theme2 v2
```

Those two imports may resolve to different cached realm snapshots if the local
scope gives them distinct aliases. The manifest should not collapse them into
one realm-wide dependency entry.

This split is required because Yulang can run a single `.yu` file without a
project lock file. Such a file still needs to resolve `std` and local/cached
realms. The resolver should therefore be able to read a source file, resolve its
requests, and cache the exact result without first requiring a human-readable
lock. A lock is a reproducibility and audit artifact, not the only exact
resolution store.

Detailed per-file resolution graphs are allowed to be too verbose for humans to
read directly. They can be surfaced through LSP, diagnostics, and
`--explain-cache`-style tools rather than copied verbatim into a hand-edited
manifest.

### Same-Realm Lookup

Same-realm imports use the same resolved realm snapshot:

```text
yulang@0.1.3/std::prelude
  -> yulang@0.1.3/ui::widget
```

The surface form must use the explicit current-realm qualifier:

```yulang
use realm/ui::widget
use realm/tools/parser::json::value
use realm/path/to/band::foo::bar
```

The current band root can be addressed explicitly with `band::`:

```yulang
use band::path::to::func
```

A bare `ui::widget` path is resolved inside the current band. It is not retried
as a same-realm band import if local lookup fails.

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

When source requests a suffix such as `v2`, it requests a version family. The
per-file resolution cache stores the exact resolved version or revision, and a
lock may record or constrain that result for reproducible runs. If two versions
from the same realm family are imported into one scope, the source must give
explicit local aliases:

```yulang
use theme/colors as theme1 v1
use theme/colors as theme2 v2
```

### `with` Version Alignment

`with` is a version alignment constraint. It is not an import by itself.

Example intent:

```text
use user/program
use ui/widget::a with program
```

The first import resolves the `program` band from the `user` realm. The second
import targets the `widget` band from the `ui` realm and asks the resolver to
use the same resolved `ui` realm version that the already resolved `program`
dependency exposes. This works only when `program` publicly exposes a matching
dependency or reexport such as `program::ui`. Private implementation
dependencies of `program` are not visible to `with`, because no outside caller
can rely on them.

Resolver rule:

```text
target import + with anchor
  -> read the anchor's public dependency / reexport surface
  -> find the target realm identity
  -> reuse the anchor-selected version
```

If the target import also requests a version family that cannot contain the
anchored exact version, the resolver should report a conflict:

```text
use ui/widget with program     # program exposes ui@1.2.0
use ui/widget v2.0 with program
                               # conflict: requested ui@2.0 family vs anchored ui@1.2.0
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
- immutable realm source digest;
- band path;
- source dependency SCC identity;
- source file identities;
- source hashes and syntax export hashes;
- dependency band interface hashes;
- dependency SCC artifact hashes;
- feature flags and relevant environment knobs.

The cache should never rely on a band path alone. A band path becomes meaningful
only after its realm has been resolved.

Cache and lock identity should use structured keys, not display paths:

```text
ResolutionRequestKey {
  resolver_format,
  importer_source_digest,
  source_site_request,
  provider_set_digest,
  anchor_public_surface_hash_if_with,
}

ResolvedRealmKey {
  locator,
  version_or_revision,
  source_digest,
}

ResolvedBandKey {
  realm,
  band_path,
}
```

The per-file resolution cache maps `ResolutionRequestKey` to
`ResolvedRealmKey`. A hit is valid only after the referenced realm snapshot and
source digest are still present and verified. The lock may record the same
resolution in a readable form, but it is not required for ordinary single-file
execution.

The digest must be strong and algorithm-tagged, such as `sha256:<hex>` or
`blake3:<hex>`. The current non-cryptographic hashes used inside in-memory
tables are not suitable for snapshot or lock integrity.

Keep hash purposes separate:

- realm content hash;
- resolution / lock hash;
- snapshot hash;
- dependency syntax / namespace / typed / coherence / runtime ABI surfaces.

Repository source providers need a stricter spec before implementation. A git
provider in `realm.toml` should identify a repository and a local name, not a
human-written version. The selected commit / snapshot and source digest belong
in `yulang.lock`, along with diagnostics that explain which part changed. A
machine-local checkout path is not dependency identity.

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
resolution/
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
.yulang/versions/<version>/
<realm>/@v/<version>/...
```

`realm.toml` declares the current realm identity when a project wants explicit
identity. It is not required to declare bands or human-written versions.
Per-file exact resolution entries live in the persistent user cache so a single
source file can run without a project lock. `yulang.lock` records resolved realm
dependencies, revisions, and frozen source hashes when a realm wants to publish
or verify its observed resolution graph. The lock file is not the primary
machine cache; it is part of reproducible source identity. Fetched realm
contents, resolution entries, and compiled artifacts live in the persistent user
cache.

`yulang realm freeze --version <version> <path>` copies the editable realm
source into `.yulang/versions/<version>/` and writes `snapshot.json` with the
exact version, file hashes, and a realm source hash. Re-running the same freeze
is a no-op when the hash matches, and a different hash for an existing version
is rejected.

The `.yulang/versions/<version>/` route is the current local implementation
shape. A future repository or standard-library layout may use a realm-owned
snapshot directory such as `std/@v/0.1.0/...`. Both are storage routes to an
immutable resolved realm snapshot; neither spelling is part of canonical
identity.

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
  source-site dependency requests, and `with` alignment constraints. This is a
  reproducibility surface, not the primary exact resolution cache.
- `collect_source_with_constraints` gathers `use ... with ...` source metadata
  into structured constraints. The resolver should be able to store the exact
  per-file result in a persistent resolution cache, and
  `YulangLockFile::from_source_set` can project the current `SourceSet` into a
  lock-shaped value for audit / reproducibility.
- local source collection reads `realm.toml` when present. The target schema
  supports `[realm]` identity and source-provider declarations. Human-written
  version requirements do not belong in this manifest; exact snapshot identity
  belongs in the per-file resolution cache and may be recorded in
  `snapshot.json` / `yulang.lock`.
- `parse_canonical_realm_path` parses the canonical
  `realm@version/band::module` shape into realm identity/version, band path, and
  module path. It keeps slashes before the final `/` inside the realm identity,
  so `user/program@2.0/ui::widget` resolves as realm `user/program`.
- `use github.com/user/ui/widget::button v1.2` parses the trailing `v...`
  suffix as source
  metadata (`realm_version`) without adding it to the normal import path. A
  suffix on a grouped item wins over an outer group suffix; the outer suffix
  fills only imports without an item suffix. The ordinary lowerer ignores the
  suffix, while lock constraint collection can preserve it as a version-family
  request before resolution.
- `yulang lock <path>` writes the current lock-shaped source graph to the entry
  realm root's `yulang.lock` (or `--out PATH`). `yulang lock <path> --check`
  reads the lock file, validates its `with` constraints, and fails if the
  generated graph would change it.
- source collection can resolve cross-realm `use` when the target realm already
  exists locally. It first tries the per-file resolution cache and verified
  realm snapshots, then consults `yulang.lock` when present, then falls back to
  manifest-declared source providers, `search_paths`, local
  `.yulang/versions/<version>/` snapshots, or the persistent `realms/` cache.
  Loaded files keep their source-level import path for lowering while their
  `ResolvedBandId` is assigned inside the target realm.
- `use ... with anchor` can use `yulang.lock` `with_constraints` to choose the
  same resolved target realm version as the anchor. When source collection loads
  that realm, generated lock output records the resolved target version even if
  the `use` omitted an explicit suffix.
- generated locks record frozen realm snapshot source hashes, and locked realm
  imports reject a source path whose `snapshot.json` hash no longer matches.
  Cached resolution entries also verify the referenced `snapshot.json` hash
  before reuse.
- version-family requests come from source imports, not from `realm.toml`.
  The local resolver may match those requests against already-present editable
  realms, frozen snapshots, and persistent cache entries. Full registry solving
  and inequality sets such as `<3` are still deferred.
- files loaded only through `use` start separate bands in the same realm for
  now.
- inline source loading creates an `embedded:inline` realm and assigns bands by
  the same `mod` edge rule.

This is intentionally still mostly an identity and storage layer. It does not
yet fetch git dependencies, implement full registry version solving for
manifest requirements, or automatically use the persistent compiled-unit cache
during lowering.

Resolver work can then proceed in phases:

1. local realm and virtual single-file realm;
2. local bands from `mod` edges;
3. `realm/band::module` absolute lookup from the current realm;
4. canonical path parser for `realm@version/band::module`;
5. version suffix extraction from CST into structured resolver metadata;
6. realm manifest and lock file;
7. cross-realm `use` resolution for already-local realms;
8. `with` version alignment constraints;
9. git / GitHub realm fetch;
10. persistent realm fetch cache;
11. compiled artifact cache lookup / invalidation in the source lowering
    pipeline;
12. browser embedded realms and IndexedDB/local storage cache.

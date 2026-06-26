# Local Realm / Band Identity

This document fixes the release-target source identity rules for local Yulang
files. It covers editable realms, bands, entry files, and the path syntax that
is already implemented for local source collection and compiled-unit cache.

It does not define the future global dependency resolver, remote repository
providers, version-family solving, or the final lock-file UI.

## Terms

A realm is a versioned resolution space. A band is an import/build island
inside one realm. A module is a namespace path inside one band.

The implementation should keep these identities separate:

```text
RealmId / BandPath :: ModulePath
```

`/` separates the realm-side band path from the module path. `::` stays inside a
band and is also the normal module / value / type separator.

## Editable Realm Boundary

Every source file is interpreted inside a realm. For local files, the editable
realm root is chosen as follows:

1. If the entry file is under a directory containing `realm.toml`, the nearest
   such ancestor is the explicit editable realm root.
2. Otherwise, the entry file's parent directory is an implicit editable realm.

The implicit editable realm is a resolution space, not a directory scan. Sibling
`.yu` files are loaded only when the source explicitly imports them with a
current-realm route such as `realm/helper::value`.

This keeps a one-file script as a one-file program while still allowing small
multi-file scripts without a manifest.

## Band Roots

The band path of a root source file is its `.yu` path relative to the editable
realm root, without the extension:

```text
main.yu          band main
helper.yu        band helper
tools/parser.yu  band tools/parser
```

`mod` grows the current band. It does not create a new band. Under the current
source layout, `mod child` may load a same-band child source such as:

```text
child.yu
current_file_stem/child.yu
```

A source file cannot be both a band root and a child module of another band. If
the collector sees one physical file claimed by incompatible band/module
identities, it rejects the source set instead of choosing a precedence rule.

Cross-band dependencies inside one realm must be acyclic. Same-band module
cycles remain a separate source-dependency question.

## Entry Band Identity

The entry file is the execution root module:

```text
module_path = <root>
```

It also owns the real band identity derived from its file path:

```text
main.yu -> band_path = main
```

This means `main.yu` can be addressed by other bands as `realm/main::...`.
Inside the entry band, `realm/main::...` is an alias back to the root module. It
does not load `main.yu` a second time, and the self-edge is not a cross-band
cycle.

The alias is route-aware:

- `realm/<entry-band>::...` strips the entry band prefix and resolves from the
  root module;
- bare `main::...` remains ordinary same-band module lookup and does not gain
  band visibility;
- `band::...` inside the entry band resolves from the root module;
- `realm/<other-band>::...` still records a cross-band dependency edge.

## Path Routes

Bare paths stay inside the current band:

```yulang
use foo::bar
```

The compiler must not retry `foo::bar` as a same-realm band import if same-band
lookup fails.

The reserved `band` qualifier starts at the current band root:

```yulang
use band::inner::value
```

Same-realm cross-band imports use the reserved `realm/` qualifier:

```yulang
use realm/helper::answer
use realm/tools/parser::json::value
use realm/path/to/band::foo::bar
```

The separator rule is:

```text
before the band boundary: /
inside the band:          ::
```

`std::...` is a prebound alias for the standard library band. It is not a
generic fallback rule for arbitrary same-realm bands.

Installed local realms use the `local/` provider prefix:

```yulang
use local/theme/colors::palette v1.0.0
use local/theme/colors::*
```

The path before `::` is provider / realm name / band path. Yulang resolves the
longest installed local realm name and treats the remaining slash path as the
band root. The version suffix is an import-site request; `v1.0.0` resolves to
the installed snapshot version `1.0.0`.

If no version suffix is present, the current implementation picks the highest
installed version string for that local realm name. This is a local development
convenience, not the final version-family solver.

## Editable Manifest And Install

`realm.toml` may declare the editable realm boundary and local install identity:

```toml
[realm]
name = "theme"
version = "1.0.0"
```

`name` is the local installed name under the `local/` provider. If no explicit
`identity` is present, the source identity is derived as `local/<name>`.

`version` is the editable realm's own release candidate version. It is not a
dependency requirement and it does not introduce a realm-wide package graph.
Human-written `[dependencies]` remains rejected; dependency requests belong to
source imports and the per-site resolution cache.

`yulang realm install <path> [--version <version>]` freezes the editable realm
and installs the frozen snapshot into the user library:

```text
$YULANG_LIB_DIR/realms/local/<name>/<version>/
```

If `--version` is omitted, `[realm] version` is used. If both are present and
differ, installation fails. The copied frozen `realm.toml` omits `version`; the
installed `snapshot.json` is the source of truth for snapshot identity, version,
and source hash.

## Visibility

Within a band, `our` and `pub` are visible according to the normal module rules.
Across a band boundary, only public dependency surfaces are alignment anchors
and importable API. Private `my` definitions are never exposed by a band import.

This rule matters for both explicit imports and future release/freeze
resolution. A private dependency is not a reason to force two realm versions to
align.

## Ambient Empty-Band Modules

The standard library is compiled as an empty-band ambient prefix. Same-band
module traversal may step into an empty-band child module from any parent band,
while non-empty bands must still match normally.

This is a reuse rule for prebound ambient modules such as `std`. It is not a
permission for user bare paths to cross between non-empty bands.

## Cache And Release Artifacts

Compiled-unit `.yucu` artifacts record source identity, including the band path
needed to resolve route-aware syntax and namespace imports from cached prefixes.

When a realm version is fixed for release, the release command should
materialize `.yucu` artifacts for released band roots:

```text
release snapshot = source snapshot + resolution metadata + .yucu artifacts
```

`.yucu` artifacts are dependency-prefix cache artifacts, not the semantic source
of truth. The source snapshot and resolution metadata define the release. If a
`.yucu` file is missing or stale, the compiler may rebuild it from the fixed
source snapshot.

Exact-program caches such as `.yuir`, `.yumo`, and `.yuvm` should not be
published as default realm release artifacts.

## Stable Scope For This Release

Stable for the local release target:

- implicit editable realm from the entry file's parent directory;
- explicit editable realm boundary at nearest `realm.toml`;
- root-file band identity derived from relative `.yu` path;
- `realm/...::...` current-realm imports;
- `band::...` current-band absolute imports;
- entry-band self aliasing without duplicate load;
- ambient empty-band standard library prefix;
- local installed realms under `local/<name>/<band>::...`;
- `yulang realm install` as freeze plus local user-library install;
- `.yucu` compiled-unit artifacts carrying band identity.

Still experimental:

- global/remote realm provider syntax;
- exact version-family solving;
- human-facing lock-file format;
- remote release/freeze command UX;
- registry and git source provider policy.

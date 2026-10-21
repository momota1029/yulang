# R293 — exact source export owners in provider artifacts

Status: solo source-identity implementation evidence; unreviewed; R149 remains OPEN.

## Result

Added `resolve_source_export_owner` to join a resolved public export to one exact
provider declaration. Binding joins require one provider `HirModule` with the
exact module label, public visibility, name, source range, and parse-owned
`SourceNodeKey`. Role joins use the existing `SourceRoleImplIndex` because a
role declaration is retained there as source syntax rather than as a value
binding. Both branches fail closed on duplicate providers, stale identities,
and unsupported declaration kinds. The API gives no type/scheme, role
conformance, implementation selection, candidate inference, or runtime fact.

The pinned closure test constructs each export index and its provider artifact
from the same `ParsedFile`. Re-parsing the same bytes creates a different
parse-owned identity and is correctly rejected. The exact pinned `println`
export joins to its public binding in `std::io::console`; `Display` joins to
its public role in `std::core::fmt`.

The same pinned resolver finds `say` at `std::io::console`, but the current
provider `HirModule` has no admitted binding for that source declaration. Its
source text is `pub say(value: 'a): () =` with a declaration `where 'a: Display`
and body `out::write: value.show`; the module HIR currently retains `print` and
`println` but not `say`. The owner join therefore returns `StaleDeclaration`.
This is a concrete remaining source-to-HIR seam on the Console critical path,
not permission to synthesize a binding or select a method by spelling.

The existing source role/implementation index can retain `Display` without
lowering all of `fmt.yu` as local value source. A trial full local-source lower
of that module returned `StructuralProjection`; that route is not needed for
the exact role identity join. The source export index remains the authority for
the public route, while this new function checks only the direct declaration
owner.

## Evidence

- `cargo test -p yu-hir --lib` — 147 passed.
- `cargo test -p yu-playground --lib pinned_public_export_route_retains_source_owned_edges_and_names -- --nocapture` — passed; checks `println`, `Display`, missing `say` owner, stale range, and duplicate provider rejection against all 40 pinned module indexes.
- `cargo check -p yu-hir` — passed with existing warnings.
- `git diff --check` — passed.

These checks establish source-owner correspondence only. They do not run either
unchanged sample and do not close R149 source adequacy, imported type/scheme
ownership, role selection, runtime output, or the original A/B proof obligations.

## Next source owner

Trace why the exact public `say` binding is absent from provider HIR, then retain
its declaration-local source carrier and prerequisite `Display` identity
without making that carrier a selected implementation. After that, the
multi-HIR solver still needs one authoritative owner for the imported binding's
type/scheme and its actual source dependencies.

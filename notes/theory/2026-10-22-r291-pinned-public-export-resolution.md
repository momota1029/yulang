# R291 — Pinned public export resolution

## Result

R290 retained parse-owned declarations and `use` trees but did not interpret
public re-export paths. R291 adds a finite-source resolver in
`crates/yu-hir/src/module/source_exports.rs` and exercises it against every
module in the exact pinned Yulang2 standard-library closure.

The resolver returns a direct declaration together with each traversed public
use leaf. The pinned closure resolves:

| Requested name | Direct declaration | Re-export route |
| --- | --- | --- |
| `Display` | `std::core::fmt::Display` | `std::prelude` → `std::core::fmt` |
| `say` | `std::io::console::say` | `std::prelude` → `std::io` → `std::io::console` |
| `println` | `std::io::console::println` | `std::prelude` → `std::io` → `std::io::console` |

Each module index retains its `ModuleId`, parse-owned source keys, exact source
ranges and text. A route is not accepted from a spelling match alone. Missing
modules and exports, duplicate module indexes, ambiguous declarations,
recovered syntax and unsupported use-tree shapes return explicit errors.
Private re-exports do not contribute an export. A visited `(module, exposed
name)` set makes cycles finite without manufacturing a declaration.

## Finite algorithm argument

`flatten_tree` follows the finite parsed `UseTree` structure by structural
recursion. At each node it appends the node's path segments to the inherited
prefix. A group recursively visits each child with that prefix; a name or glob
emits one leaf containing the complete path, selected name or exclusions,
alias, visibility, declaration owner and exact leaf source key. Recovered or
unsupported shapes return an error rather than an empty leaf set. This gives a
finite structural induction argument for the emitted syntax facts. It does
not prove the Yulang2 compiler assigns those facts the same import semantics.

Resolution walks only indexes supplied by the caller. Each recursive step adds
the current `(module, name)` pair to `visited`; later visits to that pair stop.
The set of pairs is finite because both module indexes and the requested name
are finite. Direct declarations found through multiple routes are deduplicated
by declaration identity. Parser-owned declarations use their `SourceNodeKey`;
host-act member records use `(SourceNodeKey, exact source range)` because the
parser currently represents the outer host-act as one binding node and does
not create a node for every member. Distinct declaration identities remain
ambiguous.

The resolver trusts the finite index set supplied by its caller. In the
playground test, that set is the exact pinned reachable closure. The resolver
does not itself verify the blob hash of each index or prove that every
intermediate module declaration is public. A production module resolver still
needs those checks before these source facts can authorize an import.

## Host-act source facts

For `lib/std/io/file.yu`, the parsed outer node for `pub host act file:` does
not cover the complete body. The indexer reads the indented body lines from
the original source and records public member names with their exact byte
ranges and text. All eight public members in that pinned act have distinct
ranges and retain the outer act's parse-owned source key. This is a narrow
source scanner over one parser-owned declaration, not a claim that those
members are parser nodes or HIR declarations. Malformed or changed source is
not promoted to source/native conformance by these records.

Enum variants are indexed in a virtual `module::enum` namespace, and host-act
members in `module::act`; these namespaces let pinned `use` paths reach their
source declarations. They do not create type identities, role conformance, or
runtime capabilities.

## HIR boundary and open proof premises

The resolver is exported through `yu_hir::shadow`, but it is not yet used to
bind imported names in HIR. `SemanticImports` currently carries only optional
opaque caller evidence for an exact local binding. `namespace()` constructs
`DefId`s only from local binding plans, and local-source name lowering returns
`Unresolved` when a spelling is absent from that namespace. A public role
declaration also needs semantic role identity and a type/implementation
environment; a public `say` binding needs its declaration type and scheme.
This resolver result alone supplies neither. Adding it directly to
`SemanticImports` would authenticate source provenance while still leaving
name-to-HIR and type ownership undefined.

Therefore this sprint closes only finite syntax flattening and source export
resolution for the pinned indexes. It does not close the compiler's module
map, imported-name HIR binding, role conformance, candidate typing, runtime
execution, or the original source/native proof. R149 remains open; unchanged
Types and Console samples still do not run through ordinary tests by virtue of
this result.

## Evidence

- `cargo test -p yu-hir module::source_exports::tests::public_export_resolution -- --nocapture` — 2 passed, including ambiguity/private/recovery and cycle termination.
- `cargo test -p yu-playground --lib pinned_public_export_route_retains_source_owned_edges_and_names` — 1 passed against all 40 pinned modules.
- `cargo test -p yu-playground --lib` — 31 passed.
- `cargo check -p yu-hir` — passed.
- `python3 tools/agent_sprint.py check` — static check passed; not independent review or live execution.
- `git diff --check` — passed before final note creation; rerun at checkpoint.

Warnings from existing HIR, solver and playground code remain. No independent
review lane was available under the user's solo-work constraint, so this is
unreviewed research evidence rather than production approval.

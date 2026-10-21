# R290 — Pinned stdlib export syntax identities

Status: source-index implementation evidence; solo and unreviewed. This does
not resolve imports or establish source adequacy.

## Result

Added a source-only index for declarations and import syntax. Each retained
declaration and use-tree node carries its parse-owned `SourceNodeKey`, syntax
kind, exact source range and text, and recovery status. Declarations also carry
their syntactic name and whether their source text begins with the `pub`
visibility marker. Use declarations retain the complete nested syntax-node
shape, so groups, paths, aliases, and globs remain distinguishable and ordered.

The pinned source check ties the relevant facts to these exact modules:

- `std::prelude` contains public use declarations for `std::core::fmt::*` and
  `std::io::*`.
- `std::io` contains a public use declaration for `std::io::console::*`.
- `std::io::console` contains public, non-recovered `say` and `println`
  declarations.
- `std::core::fmt` contains a public, non-recovered `Display` role declaration.

These are source facts with identities anchored to each pinned module. The index
does not expand globs, follow re-exports, determine visibility, resolve a
compiler name, or establish member selection. The import route is therefore a
source map for the next resolver step, not an authenticated semantic lookup.

## Structural argument

The use-tree retention function visits each syntax child in source order and
emits one record for each input node. At each node it copies the node kind,
parse-owned key, range, text, and recovery observation, then recursively retains
all child nodes. By induction on the finite syntax tree, every node and every
ordered parent-child edge in the input tree occurs exactly once in the retained
tree with these fields preserved. The root declaration retains its public
marker and source identity. This establishes syntax correspondence only; it
does not prove an interpretation of the tree as import semantics.

## Evidence

- Focused HIR test:
  `cargo test -p yu-hir module::source_exports::tests::public_declarations_and_use_tree_keep_parse_owned_structure -- --nocapture`
  — passed.
- Focused pinned-source test:
  `cargo test -p yu-playground pinned_public_export_route_retains_source_owned_edges_and_names -- --nocapture`
  — passed.
- `cargo check -p yu-hir` — passed.
- `cargo test -p yu-playground --lib` — passed, 31 tests.
- `python3 tools/agent_sprint.py check` — static check passed; not independent
  review or live execution.
- `git diff --check` — passed.
- Static source identity checks assert each returned key belongs to its parsed
  file and each stored range selects the exact stored text.

Existing unrelated compiler warnings remain.

## Remaining parent obligations

Implement an import-tree interpreter and pinned-module export resolver that
fails closed on recovered, private, missing, ambiguous, or changed facts. Then
connect authenticated imported identities to HIR name resolution,
`FieldTail`/role-member resolution, candidate constraints, runtime capability,
the unchanged Types and Console outputs, and the original source/native proof
obligations. Tuple plumbing already exists and is not the current obstruction.

No claim here closes the Simple-sub A/B claims, source adequacy, principal
types, effect behavior, runtime correspondence, or production readiness.

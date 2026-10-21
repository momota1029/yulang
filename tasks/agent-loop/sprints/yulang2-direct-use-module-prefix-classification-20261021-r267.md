# R267 — classify direct-use module prefixes and selected items

Status: ACTIVE primary-only source investigation.
Branch / baseline: `research/simple-sub-intrusion` / `651dbddc7`.
Authority: unchanged Types/Console goal; R149 and R261-R266. This packet
classifies source routes only; it does not define Y2 import semantics.

## Outcome

Use the source-exact direct `UseDeclaration` CSTs from R266 to resolve the
longest prefix of each explicit `std::...` route against the authenticated
40-module path set. Separate selected items inside grouped imports and
unresolved or module-local routes such as `clock::*`. Report all route nodes
and exact unresolved cases. Do not count a prefix as a semantic import edge
unless the route's CST shape supports that interpretation.

Success evidence: all direct `UseDeclaration` and `UsePath` nodes are covered;
every `std::...` route either resolves to an exact pinned module prefix or is
reported unresolved; local routes are kept distinct; grouped forms identify
their base module and selected items without losing source order. Any route
shape that cannot be classified falsifies a complete route map.

## Scope and resources

Read-only primary probe using the pinned bundle, existing `resolve_import_module`
helper and `UseDeclaration`/`UsePath` CST owner. A temporary focused test may
be used and must be removed. No retained code/tests, sample execution, build
beyond one focused Cargo test, external reads or semantics edits. Cap 420
seconds, no carryover. No independent reviewer; evidence remains provisional.

Even a complete prefix map does not prove re-export/import evaluation,
ModuleMap registration, DefId identity, runtime root publication, accepted
Types, output, parent proofs, soundness, principality or production. Those
R149 gates remain OPEN.

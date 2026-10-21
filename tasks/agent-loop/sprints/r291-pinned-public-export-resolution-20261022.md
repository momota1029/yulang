# R291 — Resolve public exports across pinned Y2 modules

Status: solo primary continuation; user goal forbids subagents, so dispatch is
degraded serial and the primary records the candidate directly.
Baseline: `2ef67dde1`.
Parent: R149 unchanged Y2 Types and Console samples, then the original source /
native proof obligations. The sample files, expected public types and output
bytes remain unchanged.

## Outcome

Turn R290's parse-owned declaration and use-tree facts into a source-qualified
resolver for public exports across the exact pinned stdlib closure. Resolve the
source identities of `Display` through `std::prelude` and `say` / `println`
through `std::prelude` -> `std::io` -> `std::io::console`. Each result must
identify its direct declaration and the exact re-export use nodes. Preserve
ambiguity and recovery as explicit failure; a name match alone never authenticates
an export.

Apply the resolver to the current HIR seam where possible without adding a
spelling-based builtin or asserting role conformance, implementation selection,
candidate typing, or runtime capability. If `SemanticImports` cannot yet carry
these authentic identities without changing unrelated semantics, expose the
resolver result to the source/candidate boundary and record that exact bridge as
the next open premise.

## Proof obligations and falsifiers

Flatten each parsed `UseTree` by structural recursion, carrying the accumulated
path through groups. Prove by induction that each emitted leaf preserves the
input path, selected name/alias/glob and exclusions, visibility, source owner,
and recovery status. Resolve only public facts from the exact module index.
Deduplicate routes only when they end at the identical source declaration
identity. For parser-owned declarations that identity is the source key; for
host-act members represented by an exact source span under a parser-owned act
node, it is the pair `(source key, range)`. Distinct declarations are ambiguous.

Fail closed for a missing supplied module/name, malformed or unsupported use
shape on a candidate route, recovered declaration/use on a required route,
private re-export, duplicate module identity, ambiguous declaration, or
source-key/range mismatch. The caller supplies the finite module indexes; the
resolver itself does not authenticate pinned blob hashes or prove visibility
of intermediate module declarations. The pinned test harness supplies the
exact reachable bundle, while module-path visibility remains an open premise.
Cycles terminate through a visited `(module, exposed-name)` set; they do not
create an export by themselves.

The proof is only for the finite syntax flattening and resolver algorithm over
the retained source index. It does not prove that Yulang2's compiler imports,
HIR, type rules, candidate solver, or runtime implement the same semantics.
Tests check exact pinned source identities and failure cases; they are not the
source/native proof.

## Evidence and stop boundary

Before/after evidence: R290 retained exact source syntax but had no import
interpreter. Success requires unique source declaration results for the three
named symbols and useful fail-closed counterexamples for ambiguity/recovery.
Record unsupported pinned grammar instead of silently treating it as no export.

Inspect the existing semantic import carrier, source role/member resolution and
playground module path. Make the smallest owner-local integration that preserves
source occurrence and module identity. Continue into the next closely related
HIR/candidate step under these same leases if a result becomes usable; do not
stop after writing a resolver-only note while the sample path remains reachable.

## Leases and resources

Exact paths: `crates/yu-hir/src/module.rs`,
`crates/yu-hir/src/module/source_exports.rs`, `crates/yu-hir/src/shadow.rs`,
`tools/inference-playground/src/lib.rs`,
`tasks/agent-loop/current.json`, this contract, and
`notes/theory/2026-10-22-r291-pinned-public-export-resolution.md`.

Cap 900 seconds, no carryover, one Cargo process at a time. Check focused
source-index/resolver tests, full `yu-playground` library tests,
`cargo check -p yu-hir`, `python3 tools/agent_sprint.py check`, and
`git diff --check`. No independent review in the user-authorized solo setup;
freeze as unreviewed research evidence and keep R149 open. Stop at budget,
resource failure, or a semantic ownership change beyond this contract; next
consultation boundary is resolver-to-HIR/candidate import integration.

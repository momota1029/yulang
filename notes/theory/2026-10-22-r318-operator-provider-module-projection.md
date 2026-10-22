# R318 — operator provider HIR projection

Status: OPEN_CONTINUATION. This receipt records a bounded source projection result; it does not close candidate typing, any A/B proof, R149, or production.

## Entry

R316 authenticates imported operator declaration/body source identity. R317 joins that receipt to the exact existing provider `SourceRootId::Expression` and LocalSource carrier. The pinned provider projection still traverses only imported value names, so it can omit `core/ops` from the solver's multi-module source world.

## Bounded objective

Follow imported operator-use provenance in retained consumer LocalSource, resolve it through the exact syntax import environment, and add the selected provider RHS source root to the provider module's selected-root projection. Merge that root with ordinary value roots already selected from the same module. Preserve the provider's original ParsedFile and parse-branded keys.

This source-world extension assigns no operator scheme, type, receiver choice, or runtime meaning. Consumer infix candidate admission and the original Y2 sample remain open.

## Result

`pinned_provider_projection` now scans retained top-level and member `LocalSource` roots for imported infix operators. Each use is resolved through the consumer's exact `SourceImportEnvironment`; the selected index must uniquely match the owner's module, revision, declaration, spelling, and fixity. The provider identity and parsed file must own the receipt's declaration and body keys. The body key is added to the same per-module selected-root set used for imported value exports, and the existing parse is lowered under that combined selection.

The regression uses a retained member-body infix operator and checks that projection includes exactly one module for its owner and that `source_operator_root_for` returns the original provider body range and source text `\\x -> \\y -> x.add y`. The existing ordinary imported-value projection regression remains separate; the pinned operator provider exposes operator declarations rather than an ordinary binding root for this fixture.

Verification: focused operator projection test passed; `cargo test -p yu-playground --lib` passed 42/42; `python3 tools/agent_sprint.py check` and `git diff --check` passed. Existing `yu-hir` and `yu-solver` dependency warnings appeared during compilation and remain a separately owned audit item. No independent review was run; the result is solo and unreviewed.

## Proof correspondence

For every projected operator root, retain the chain:

1. consumer occurrence and selected imported `HirOperator` provenance;
2. exact `SourceOperatorOwner` from the selected dependency route and provider index;
3. exact provider HIR root returned by R317 for that same index and parse;
4. selected provider module included in the candidate HIR world.

A projection result is invalid if any link is absent or ambiguous. Same spelling alone contributes no edge.

## Falsifiers and next gate

Wrong dependency/index, parse-brand mismatch, duplicate root, or dropped existing imported-value root falsifies the projection. The next gate consumes the projected provider expression as an operator value in Candidate Apply while preserving the consumer occurrence, operands, per-use generalization and effects. No theorem or production gate is closed here.

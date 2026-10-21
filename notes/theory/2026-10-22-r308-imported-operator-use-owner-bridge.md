# R308 — imported operator-use owner bridge

Status: READY, solo and unreviewed; parent R149 remains OPEN.
Baseline: `76cb4ea7a`.

## Governing design reread

Reread the converted unified design §§4.1–4.5, §5.1, §6 and method stage 4, plus proof companion §§3–4, §§7–8. Source identity, current endpoints and semantic payload remain distinct. A selected declaration does not follow from a spelling match; candidate selection still waits for settled bounds. A local source correspondence does not close Capture/FreshUse or source/native obligations.

The effect correction remains explicit: contravariant `[io]` abbreviates `[io,'e]`; passing `[state]` alone is not an effect violation. Permission does not erase actual contributions.

## Entry and selected bridge

R306 authenticated the pinned fmt glob dependency and traced the original `Display.say` plus token to imported Infix provenance for `lib/std/core/ops.yu`. R307 indexed the exact provider `OperatorHeader` and adjacent original body `OperatorChain`, retaining separate parse-owned keys, ranges, metadata and text. Its pinned check confirms `\\x -> \\y -> x.add y` under the resolver-supplied dependency revision.

The remaining source seam is the join from the consumer's imported operator receipt to that provider index. R308 retains owner records only for selected syntax dependencies whose provider path and revision match, then resolves by declaration range plus spelling/fixity. No fallback by spelling is allowed. Local and imported use identities remain distinct from the provider's declaration and body identities. A dedicated syntax-only view carries no ordinary value import bindings, so it cannot be mistaken for the normal value-import environment.

Attempting to build full `SemanticImports` for pinned fmt returned `SourceImportResolutionUnavailable`. The exact failing value import was not isolated in R308; the syntax-only view keeps the operator source correspondence independently observable without claiming that the value-import route is complete.

## Parent application boundary

If this join succeeds on the unchanged pinned source, the source path reaches the exact operator value body without assigning that value a candidate scheme or method meaning. The next required owners are source candidate formation and the original FieldTail/member constraints; those must preserve receiver bounds and deferred readiness. The unchanged Types and Console samples, source/native proof, A/B, principality, termination, review and production remain OPEN. R149 remains OPEN.

## R308 evidence

The pinned `Display.say` regression resolves the HIR Infix `+` declaration receipt through a syntax-only `SourceImportEnvironment` to the exact pinned RHS `\\x -> \\y -> x.add y`. It rejects a shifted provider range, wrong spelling/fixity, a provider index whose revision label is wrong, and an index whose module path is changed. Existing R307 tests cover duplicate ambiguity, recovery, parse-owned declaration/body keys and exact pinned byte slices. Consumer use range and provider declaration range remain separate values.

## R308 result

Provider operator source records are retained from indexes matching the consumer parse's selected syntax dependency path and revision; index and record module/revision identities must agree. `SourceImportEnvironment::for_syntax_operators` exposes this as a syntax-only source view with no value-import names. Existing SemanticImports constructors also carry the selected operator records alongside their separate value/role imports.

`operator_body_for_use` requires imported provenance, exact dependency path/revision, provider declaration range, spelling and fixity, and exactly one public, unrecovered match. The unchanged pinned `Display.say` `+` resolves to `\\x -> \\y -> x.add y`. Focused negatives pass for wrong module path, revision, declaration range, spelling and fixity. Source key ownership and duplicate/recovery rejection remain covered by the R307 HIR tests.

Full `SemanticImports` construction for pinned fmt returns `SourceImportResolutionUnavailable` on the full `use` surface. The cause was not isolated here. R308's dedicated syntax-only view leaves that value-import result untouched and does not represent it as resolved.

The pinned source-owner test, HIR source-export tests, both crate checks and unchanged Types/Console boundary tests pass. R308 remains solo and unreviewed. This bridge identifies source bytes only; it assigns no operator value type, candidate, method meaning or selection. The original source/native theorem and R149 remain OPEN.

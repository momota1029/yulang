# R268 — compare source module declarations and imports to the pinned closure

Status: ACTIVE primary-only source graph check.
Branch / baseline: `research/simple-sub-intrusion` / `51a1aeef7`.
Authority: unchanged Types/Console goal; R149 and R261-R267. This graph is a
source locator, not approved Y2 loader semantics.

## Outcome

Combine direct external `mod` declarations with the R267 longest-prefix
`std::` use edges. Starting at implicit module `std`, compute the reachable
module paths and compare them to the authenticated 40-source bundle. Keep
source-order edge records and report unresolved module declarations/routes.
Do not treat graph reachability as import visibility, registration, evaluation
order, or runtime publication.

Success evidence: all 40 blob IDs authenticate; each direct `mod` name maps to
an exact pinned child path or is reported unresolved; all 108 `std::` base
routes are source-bound; BFS reachability reports missing/excess module paths
relative to the 40-source set. Falsifiers include a route with no module
prefix, missing source identity, or graph closure mismatch.

## Scope and resources

Read-only probe over the pinned bundle and current CST owners for
`ModDeclaration` and `UseDeclaration`. One temporary focused Cargo test may be
used and must be removed. No retained code/tests, semantic edits, builds beyond
that test, sample execution, or external reads. Cap 420 seconds, no carryover.
Primary-only and unreviewed.

R149 module identity/publication, accepted Types, Request reachability, outputs,
Simple-sub/evaluator A/B, R70/R71, source/native proofs, soundness,
principality and production remain OPEN.

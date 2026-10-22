# R316 — authenticated operator value owner

## Entry

R315 now preserves the exact parser-associated four-infix tree in the pinned ordered-pair `Display.show` carrier. Candidate collection still rejects `InfixOperator`. The operator parser receipt identifies the selected declaration site and imported syntax dependency, and R308 resolves that route to the exact public provider declaration/body, but the consumer-facing API returns only body text.

## Bounded target

Expose the exact provider operator owner as an immutable source receipt derived from the existing imported `HirOperator` provenance and `SourceImportEnvironment` records. Keep the consumer token/use key distinct from provider declaration/body keys. Preserve module, revision, declaration/body source keys and ranges, spelling, fixity, visibility and lazy metadata. Resolution must remain unique and fail closed for mismatches, recovery, visibility, and ambiguity.

This receipt proves source ownership only. It supplies no operator value type or candidate scheme, performs no `+` to `.add` rewriting, and does not admit, type or select an infix use. The candidate collector's `Unavailable` boundary and the unchanged Types sample's deferred selection remain until a later source-to-candidate bridge consumes this exact owner.

## Outcome

`SourceOperatorOwner` now carries provider module/revision, exact declaration/body `SourceNodeKey`s and ranges, spelling, syntax fixity, visibility and lazy metadata. `SourceOperatorOwner` is exposed through both `SourceExportIndex::operator_owner_for_receipt` and `SourceImportEnvironment::operator_owner_for_use`. The imported-use API delegates to the same exact route check as the existing body-text method, so local provenance, wrong module/revision/range, metadata mismatch, ambiguity and recovered body still fail closed.

The pinned integration compares the imported-use receipt with the receipt from the exact selected provider index and verifies that the keys are foreign to the consumer parse. The first test attempt compared them with a newly parsed copy of identical bytes and failed: `SourceNodeKey` includes the parse product brand. The test now uses the actual index that minted the provider keys, which is the correct identity boundary.

Verification: `cargo test -p yu-hir --lib` — 165 passed; `cargo test -p yu-playground --lib` — 41 passed; focused private-operator receipt rejection and `pinned_stdlib_role_impl_sources_keep_distinct_module_identities` passed. The ordinary Types sample remains deferred at candidate FieldTail/infix admission. Candidate collection still rejects `InfixOperator`; owner resolution does not assign a type scheme, admit or type the body, select a method, execute the sample, or close R149/source-native/A-B/principality/termination/review/production.

Git checkpoint: the R316 source-owner result was committed as `33cb23d79` (`Track authenticated operator source owners`) and pushed to `research/simple-sub-intrusion`.

The next gate is to connect the exact LocalSource operator occurrence to its provider owner and value body within candidate construction, preserving the consumer occurrence and not inventing a top-level definition. Parent R149 and all overall proof/production gates remain OPEN.

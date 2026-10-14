# Scoped effect algebra implementation and proof

Date: 2026-10-15
Status: private compiled kernel and local proof reviewed; live scoped source inference remains OPEN
Baseline: `72e156f77d32efea98eeb06b3f54a98fdc9395c0`
Authority: [selected compose behavior](../design/2026-10-15-compose-scoped-effect-release.md); reversible native experiments under the inference playground decision

## Delivered slice

`candidate_scope.rs` implements finite canonical `StampInput`, `ProtectBody`
and `Release` transformations, ordered composition, evaluation, injective
renaming and fallible retained-capacity accounting. It changes scope/tag
state only; it contains no effect members or handler grants. The module is
compiled with `shadow-apply-candidate` and explicitly allows unused code
while its native source/receipt integration remains open. It has no active
handler consumer in this checkpoint.

The [construction proof](../theory/2026-10-15-compose-scoped-release-construction.md)
derives normal-form uniqueness, composition, associativity, renaming and
scope-specific release, and maps these claims to the frozen Rust functions.
Its scheduling lemma is conditional on complete, fair two-sided replay of
full `(w,T,U)` facts. The actual native Value-entry identity chain is retained
separately from the still-missing source scope/receipt certificate.

The independent [source characterization](2026-10-15-compose-release-source-falsifier.md)
establishes that the existing direct-formal introduction records omit local
alias exposures. Absence of a record cannot be interpreted as absence of
protection. It is a static constructor result, not a runtime counterexample.

## Review and verification

M2 with two reviewers for distinct risks: `compiler_referee` reviewed the
kernel/proof pair, and `spec_auditor` reviewed the pinned source supplier
characterization. No blocking/major finding remained. The proof reviewer’s
minor request to retain the input-tag coordinate in replay identity was
repaired and checked by the primary.

`CARGO_BUILD_JOBS=2 timeout 300s cargo check -q -p yu-playground` passed, as
did the subsequent playground build including the independently reviewed
adjacent-header HIR slice. No warnings were emitted. Whitespace and proof
document structural checks passed. No tests were added/run; no benchmarks
or performance samples were taken. No live release observation or principal
scheme derivation is claimed by these compilation results.

## Current integration owner

The bounded native integration attempt identified a concrete missing owner:
scheme capture retains rows/boundaries, but not a source inventory telling
which protection scopes are local and which are inherited. Guessing from
row equality or renaming every scope would break independent protection.
The next reversible construction retains source regions and their latent
scope/route inventories, then shares one renaming map through actual FreshUse.
Native integration, source completeness, recursive receipt identity, Catch
subtraction, soundness, principality and production remain OPEN. The selected
source semantics are unchanged; the private representation is not adopted
as a completed architecture.

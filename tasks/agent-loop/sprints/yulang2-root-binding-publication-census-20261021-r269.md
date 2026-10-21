# R269 — classify pinned root bindings and publication candidates

Status: ACTIVE primary-only source census.
Branch / baseline: `research/simple-sub-intrusion` / `0cd8cdc0f`.
Authority: unchanged Types/Console goal; R149, R260, R266-R268. The exact 40-source bundle is authenticated input. Current Y3 CST structure is locator evidence only; it does not establish Y2 loader semantics or runtime publication.

## Outcome

Parse the 40 authenticated source blobs after only the documented equal-length line-leading Y2-comment projection. In source order, classify direct-root `BindingStatement` nodes by body presence, header pattern structure, and body root kinds. Count direct-root expression candidates and pair each root `OperatorChain` with its nearest preceding `OperatorHeader`/binding owner. Reconcile parsed body-bearing binding counts against R260's conditional textual census. Identify what remains needed to connect direct declarations to the existing Value/Computation root constructors.

Success evidence: per-source authentication, aggregate body/signature counts, noarg/argument-shaped binding classification with exact CST predicates, explicit unmatched/malformed direct-root candidates, operator pair coverage, and an owner-level mapping or precise missing seam to `runtime/program.rs` publication. Falsifiers include count mismatches, unclassified bodies, unpaired chains, or a publication path that cannot consume the observed declaration forms.

## Scope and resources

One temporary focused Cargo test/probe over the pinned bundle and current parser/HIR/runtime source owners; remove it after capture. No retained code/tests, semantic edits, changes to bundle resolution, sample execution, or external reads. Do not interpret aggregate Y3 parser diagnostics as Y2 compatibility because comment projection and external `mod` recoveries are known confounders. Cap 420 seconds, no carryover. Primary-only, unreviewed. Keep R149 module identity/publication, accepted Types, Request reachability, outputs, parent proofs and production OPEN.

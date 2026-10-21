# R307 — operator declaration source owner

Status: RESULT, source-owner boundary implemented; solo and unreviewed; parent R149 remains OPEN.
Baseline: commit `4588437212adf135bc74874aaba58c562aafb0c4`.

## Governing material reread

Reread the converted unified design §§4.1–4.5, 5.1, 6, stages 3–6 and §§9–10, plus the proof companion §§4.1–4.5, 5.1.1 and 2.12.1. The design keeps original identity separate from current endpoints and semantic payload. Method selection waits for relevant bounds to settle. The proof text distinguishes source-occurrence correspondence from the larger Capture and source/native theorems; a local source index does not close those premises.

The effect correction remains explicit: contravariant `[io]` stands for `[io,'e]`; passing `[state]` alone is not a violation. Permission does not erase actual effect contributions.

## Entry evidence

R305 added a read-only receipt for an already-associated `HirOperator`, carrying the selected declaration origin/range and imported syntax dependency. R306 retained the pinned fmt module globs, selected `lib/std/core/ops.yu` at its exact revision, and traced the original `Display.say` plus token through HIR to the provider `pub infix (+)` header range. The HIR receipt does not yet identify a parse-owned source declaration or its value body.

The pinned operator body is the original lambda `\\x -> \\y -> x.add y`. Its member meaning must come from the original declaration/source path; `+` does not generally mean `.add`.

## Narrow target

Build a source identity for one exact operator declaration in the pinned provider parse. Match by module identity/revision and exact declaration range, then retain the source key, visibility, spelling/fixity and original value-body range. Reject stale or mismatched sites. Keep the consumer use and provider value source distinct.

This does not create a solver root, scheme, member obligation, selected implementation, or runtime action. The next missing boundary after source identity is a source-owned candidate/scheme consumer that preserves the existing FieldTail receiver bounds and delays readiness. R149, all proof gates and production remain OPEN.

## Result

The source export index now retains a complete root `OperatorHeader` together with its adjacent `OperatorChain` body. Each side keeps its own parse-owned `SourceNodeKey`, source range and exact text; the record also carries the index module, revision, visibility, spelling, fixity and lazy bit. The resolver is keyed by module/revision and exact declaration range, then checks the receipt's spelling/fixity. Wrong module, revision, range or fixity, ambiguity, missing body and recovered body do not resolve.

The pinned `Display.say` regression follows the imported syntax dependency receipt to the exact provider declaration range and confirms that its body bytes are `\\x -> \\y -> x.add y`. `ParsedFile::revision()` remains `UNTRACKED` in this path, so the pinned caller binds the index to the revision supplied by its authenticated source resolver. This is a caller assertion about the source snapshot, not an internal hash check; the test also matches the dependency revision to the pinned bundle fingerprint and slices declaration/body text from the same provider bytes.

Checks passed: HIR source-export tests, pinned stdlib source-owner test, `cargo check -p yu-hir --features shadow`, `cargo check -p yu-playground`, and the unchanged Types deferred FieldTail boundary test. Existing unrelated compiler warnings remain. The evidence is implementation/source correspondence, solo and unreviewed. It proves no typing, execution, source/native theorem or production result; R149 and all such gates remain OPEN.

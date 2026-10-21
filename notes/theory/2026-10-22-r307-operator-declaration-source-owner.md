# R307 — operator declaration source owner

Status: READY, pinned source-owner bridge target; parent R149 remains OPEN.
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

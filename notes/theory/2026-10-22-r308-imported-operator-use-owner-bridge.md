# R308 — imported operator-use owner bridge

Status: READY, solo and unreviewed; parent R149 remains OPEN.
Baseline: `76cb4ea7a`.

## Governing design reread

Reread the converted unified design §§4.1–4.5, §5.1, §6 and method stage 4, plus proof companion §§3–4, §§7–8. Source identity, current endpoints and semantic payload remain distinct. A selected declaration does not follow from a spelling match; candidate selection still waits for settled bounds. A local source correspondence does not close Capture/FreshUse or source/native obligations.

The effect correction remains explicit: contravariant `[io]` abbreviates `[io,'e]`; passing `[state]` alone is not an effect violation. Permission does not erase actual contributions.

## Entry and selected bridge

R306 authenticated the pinned fmt glob dependency and traced the original `Display.say` plus token to imported Infix provenance for `lib/std/core/ops.yu`. R307 indexed the exact provider `OperatorHeader` and adjacent original body `OperatorChain`, retaining separate parse-owned keys, ranges, metadata and text. Its pinned check confirms `\\x -> \\y -> x.add y` under the resolver-supplied dependency revision.

The remaining source seam is the join from the consumer's imported operator receipt to that provider index. R308 retains owner records only for selected syntax dependencies whose provider module label and revision match, then resolves by declaration range plus spelling/fixity. No fallback by spelling is allowed. Local and imported use identities remain distinct from the provider's declaration and body identities.

## Parent application boundary

If this join succeeds on the unchanged pinned source, the source path reaches the exact operator value body without assigning that value a candidate scheme or method meaning. The next required owners are source candidate formation and the original FieldTail/member constraints; those must preserve receiver bounds and deferred readiness. The unchanged Types and Console samples, source/native proof, A/B, principality, termination, review and production remain OPEN. R149 remains OPEN.

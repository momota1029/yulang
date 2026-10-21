# R220 — Repeated-loop Local FreshUse route

Status: bounded candidate-only source/native lineage result. The original
computation-forwarding theorem and R71/R72 global coverage remain OPEN. No
independent review is claimed.

## Source, physical admission, and Local uses

This is the exact repeated-call source recorded in R219. Ordinary
`CandidateInference::solve(hir)` admits it without candidate errors. The loop
Lambda's local slot-4 relation has source bound
`BoundKey(Effect(EffectRow(5)), Negative, Effect(EffectRow(38)))`, physically
owned by `Effect(5)` in `EffectUpperRow[0]`.

The two source `loop z` Applies (occurrences 21 and 18) each have one retained
Local route. The source provider observer reports complete facts/origins, while
its capture-row list is truncated even at a 4096-row bound. Reading the retained
route graph's exact bounds directly still joins the source slot-4 relation to
both routes. The `FreshUse` witnesses map that original bound to:

- occurrence 21: `BoundKey(Effect(EffectRow(61)), Negative, Effect(EffectRow(57)))`;
- occurrence 18: `BoundKey(Effect(EffectRow(47)), Negative, Effect(EffectRow(43)))`.

The test checks each exact source-to-image pair in the relation lineage with
`reason: FreshUse`. This is route-level lineage evidence, not a preservation
certificate; the observer itself leaves `preservation_complete` false.

## Later consumer boundary

The complete ordinary execution trace has two `Work::Bound` events, both
source-qualified by R219 to the earlier direct `loop x` and helper-body `loop
y` checks. Neither event selects the source item `Effect(38)` or either Local
FreshUse image item `Effect(57)` / `Effect(43)`. The complete intrusion-forest
event log contains no birth or parent write for these three item rows. This
source therefore traces the retained Local/FreshUse routes but supplies no
later production `Work::Bound` consumer for those images. It is the first
remaining premise in this exact case; no third-owner alias-changing copy is
inferred.

R219 independently replayed the complete forest history to its final snapshot
for this same source. R220 rechecks forest-log completeness and the exact item
absence while joining the consumer trace to the two route images. These
case-specific observations do not prove global raw/canonical fiber coverage,
arbitrary-prefix preservation, simultaneous receivers, foreign continuations,
or semantic/production gates.

## Checks and limits

- Focused R220 route-lineage test: passed (1 test).
- `RUSTC_WRAPPER= cargo test -q -p yu-playground`: passed.
- No compiler semantics, production paths, samples or expected outputs changed.
- R218/R219/R220 are candidate-only observations; the original theorem and
  global R71/R72 obligations remain open.

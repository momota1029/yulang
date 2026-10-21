# R231 — Bounded cross-owner source schedule search

Status: bounded negative search over six accepted source variants; no independent review. It does not prove general absence or close R71/R72/the parent theorem.

## Method

The test-only `r231_cross_owner_source_schedule_variants` starts from R221's accepted `loop`/`repeat` source and varies ordinary call placement: call `loop z` inside the callback, add `loop q` before the provider call, invoke the provider twice, add a third formal callback call, forward the provider through a second formal, and pass a local wrapper around `loop` as provider. Every candidate parses without structural recovery, lowers, solves with no candidate conflicts/errors, and has a complete forest event log. The focused test also checks that every started extrusion finishes.

For each source, the trace records actual production `Work::Bound` raw keys and ordered row merges. A prefix representative map is updated at each traced effect-row merge. At each subsequent effect WorkBound, the probe checks whether its raw item has already changed representative while its owner remains outside that item class. This is the third-owner, post-alias selection predicate. The result is empty in all six cases.

| Source variation | Effect-row merges | Effect WorkBound raw slots | Third-owner post-alias hits |
|---|---|---|---|
| callback directly calls `loop z` | 39→13, 40→38 | 10/32, 24/34 | none |
| direct `loop q` before `repeat` | 39→14, 40→38 | 11/32, 22/34 | none |
| provider called twice | 41→14, 42→40 | 11/34, 22/36 | none |
| extra formal callback call | 39→13, 40→38 | 10/32, 22/34, 24/34 | none |
| provider forwarded through `relay g` | 44→14, 45→43 | 11/36, 22/38 | none |
| local `wrapped` calls `loop` | 41→14, 42→40 | 11/33, 25/36 | none |

Rows list raw owner/item ordinals; `39→13` denotes the ordered effect-row parent write. These traces show ordinary qualifying merges elsewhere in the same solve, but none changes a raw item selected by a later WorkBound in this tested family. The added callback calls produce additional WorkBound occurrences without creating the target slot alias.

## Consequence

The R221/R229 source family can connect the callback formal, provider port and exact body WorkBound, yet ordinary direct calls, repeated provider use and one extra higher-order hop still fail to produce the required cross-owner item alias. This narrows the next search: a useful source must cause the physical item's own representative to change before its later WorkBound, not merely produce unrelated row merges or another callback consumer. No source-specific required consumer is established by these six misses.

The bounded test is evidence for these exact variants only. It is not an impossibility theorem, a production regression, or evidence that every accepted source lacks the pattern. R71's all-slot fiber lineage, R72's exact later occurrence, and the original theorem remain OPEN. No production or sample code changed.

# R232 — Embedded playground sample cross-owner search

Status: finite source-corpus result; no independent review. R71/R72 and the original computation-forwarding theorem remain OPEN.

## Exact corpus and result

The test-only observer loads the four executable Yulang2 browser examples directly with `include_str!`, parses/lowers each without structural recovery, then runs ordinary `CandidateInference::solve`. All four are accepted with no solver errors or candidate conflicts, and each supplies a complete forest history.

| Embedded source | Candidate WorkBound events | Effect-row merges | Cross-owner post-alias hit |
|---|---:|---:|---|
| `yulang2-identity-island.yu` | 0 | 0 | none |
| `yulang2-ordinary-islands.yu` | 0 | 0 | none |
| `repeated-choice.yu` | 3 | 0 | none |
| `polymorphic-escaping-closure.yu` | 0 | 0 | none |

The three `repeated-choice` WorkBounds are two occurrence-6 lookups (`EffectRow(7) -> BottomPositive` owned by row 28 and `ValueRow(8) -> BoolPositive` owned by row 27) and one occurrence-31 lookup (`EffectRow(42) -> Support(0)` owned by row 43). None has a prior alias-changing parent write. Consequently there is no third-owner raw item selected after its representative changes in this exact sample corpus.

The observer reconstructs the effect-row representative map in trace order at each WorkBound. It compares the raw owner and item at that exact prefix, and accepts a hit only when the item has changed representative while the owner remains outside the item class. Forest history is complete, and every effect parent write corresponds to the ordered trace merge.

The two browser files intentionally demonstrating type diagnostics are not in the constructive corpus; their existing CLI tests check rejection. The ordinary playground package suite passed in the same source tree, so sample runtime and candidate trace evidence remain separate checks.

## Consequence and limit

The embedded examples satisfy their ordinary execution/diagnostic tests but do not contain the R71 cross-owner schedule. `repeated-choice` reaches production WorkBound without any row merge, so its actual consumer cannot witness an alias-dependent slot loss. This is useful source-domain evidence for these exact fixtures only; it is not evidence that arbitrary accepted source lacks the schedule or that a later lineage is never required.

No production or sample file changed. The next proof input must create an accepted owner constraint that both (a) stores a third-owner physical slot with item q and (b) later merges q into a, while a subsequent actual call visits the slot's owner. R71/R72 and the parent theorem remain open.

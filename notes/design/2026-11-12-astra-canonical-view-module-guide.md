# Canonical observations and the refresh-fork repair (Item 5c)

Status: **partial implementation**. The maximal certified observation predicate
and a real repair of the previous refresh fork are proved. General inspection
from that predicate, full saturation completion, and confluence remain open.
Progress/descent remains paused.

| Module under `lean/Yulang/` | Responsibility |
| --- | --- |
| `GeneralCanonicalObservations.lean` | Source-indexed scalar/normalized structural/nominal facts, certification, compatibility, full-journal entailment, maximal predicate, exact models, monotonicity, cache-only completion. |
| `GeneralNominalCanonicalViewObstructions.lean` | Both old fork endpoints are Known-maximal; the old refinement contract cannot replace the wide descriptor with the point descriptor. |
| `GeneralNominalReobservationSteps.lean` | Additive point-precision revision of nominal descriptors; model/identity/journal preservation; actual Step, Stable, closure, generated-demand and committed-packet laws. |
| `GeneralCanonicalObservationSquares.lean` | Merge/merge model and canonical-view commutation; refresh and revision preserve the canonical predicate; conditional squares for fixed information additions. |
| `GeneralNominalReobservationExamples.lean` | Certified wide-to-point repair; joinability and diagnostics of the old fork; literal single-descriptor containment obstruction. |
| `GeneralNominalReobservationBoundary.lean` | Concrete V5 boundary for this partial repair; six unconditional bridge laws. |
| `GeneralNominalReobservationExecutor.lean` | Noncomputable executor; three execution fields conditional only on its own V5 Progress field. |
| `GeneralNominalReobservationObligations.lean` | Exact four residual fields after assuming Progress; explicit halted-order residual and bridge assembly. |
| `GeneralNominalReobservationBoundaryExamples.lean` | Repaired fork in the new boundary's actual Local and diagnostic judgments. |

All nine modules are imported by `lean/Yulang.lean`. The 95 new public theorem
checks are in `lean/Audit/AstraCanonicalView.lean`. The frozen umbrella audit
and README were not edited.

The full statements and the 14-field status table are in **Item 5c** of
[the general-boundary design note](2026-11-11-astra-general-boundary.md).
The boundary is deliberately named `ReobservationBoundary`, not a completed
canonical boundary: its classifier still uses the existing finite snapshot.

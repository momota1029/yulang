# Item 4f support module guide

Status: partial proof bridge, 2026-11-12. General guarded termination remains open.

Read the [Item 4f design section](2026-11-11-astra-general-boundary.md#item-4f--retained-support-and-guarded-expansion-2026-11-12)
for semantics, theorem statements, V5 accounting, and remaining obligations.

| Module | Responsibility |
|---|---|
| `GeneralNominalPacketSupport` | Exact split of cached context, input deltas, and named materialization |
| `GeneralNominalSupport` | Immutable source, fact supports, finite discharge, query-directed reads, whole-decision guard |
| `GeneralNominalSupportChoices` | All finite support alternatives for packets/merges; tracked recovery equalities |
| `GeneralNominalSupportSteps` | Guarded feedback/reobservation steps, model correspondence, closure, guarded commitment |
| `GeneralNominalSupportBoundary` | V5 boundary, support pending below K2, six unconditional bridge fields |
| `GeneralNominalSupportGrowth` | Real R installation/refresh, first child blocked, failed modelwise rank |
| `GeneralNominalSupportInstallation` | Initial independent selected judgment yields a real guarded installation |
| `GeneralNominalSupportExamples` | Display/Wrap selection, emission and actual expansion |
| `GeneralNominalSupportExecutor` | Executor and three V5 execution fields, conditional only on Progress |

Audit part: `lean/Audit/GeneralNominalSupport.lean`. The old audit and README are frozen.

Open: installation order, guarded interval readback, sibling stabilization,
later packet/merge support rejustification, confluence, and the remaining
stable evidence/generated-child bridges. The R pending theorem is not an EOF
stability theorem. No new language decision is assumed.

# R282 primary handoff — post-parser source/HIR obstruction

Contract: `tasks/agent-loop/sprints/r282-y2-post-parser-source-hir-obstruction-20261022.md`.
Baseline: `e6b6f216b`. Primary-only read-only packet under R150 rev2 preparation; no code leases.

Exact Types and Console template hashes match R149. Types stops at the existing solver FieldTail fail-closed arm (`candidate_source.rs:1539`) despite a retained `pair.say` HIR source carrier. Console stops because `SemanticImports::empty` leaves `println` and `say` unresolved and candidate preflight rejects those names (`candidate_source.rs:500`). Exact fmt syntax now parses cleanly but full HIR lowering returns StructuralProjection; the local-source block walker has no WhereClause child case, and no HIR/solver WhereClause consumer exists. The specific HIR error enum does not expose the failing child, so that connection remains provisional.

Next code owners require a revised activated R149 contract and exact leases after the source/runtime initializer and role-resolution premises are closed. No sample output, proof closure or production promotion is claimed. The `[io]` contravariant interpretation remains `[io,'e]`.

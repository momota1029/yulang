# R299 — imported scheme and same-world inference route

Status: active implementation investigation; no proof or independent review is claimed.

## Parent and authority

R149 remains the unchanged Types/Console outcome. The converted design and proof documents require source constructor identity, constraint generation, propagation, Capture/FreshUse, publication and execution to remain one connected derivation. An imported source scheme cannot be treated as a disconnected closed-type side solver. R298 supplies only the exact role-to-provider implementation inventory; it does not select a receiver implementation or discharge a role prerequisite.

## Starting evidence

At baseline `e0b6081b4`, `CandidateInference::solve` and `ConstraintBatch` own one `Arc<HirModule>`. The HIR import environment retains authenticated `SourceExportId` routes and optional exact `SourceRoleId`s. Candidate source preflight rejects `LocalSourceResolution::Imported`; `candidate_scheme::Graph` retains role obligations and `FreshUse` maps their subject row within one session. `ClosedValueScheme` in `yu-types` is a separate arena representation and does not itself carry candidate source-role prerequisites.

These ownership facts make naive HIR concatenation and disconnected provider inference unsuitable. R299 investigates the smallest same-session multi-artifact route while preserving source-root identity and graph/FreshUse transport.

## Open obligations

- Locate and authenticate each imported binding's provider HIR declaration by `SourceExportId`.
- Let the existing candidate session own provider and consumer constraints together, or establish a source-level construction that is exactly equivalent and still uses the same graph and FreshUse maps.
- Preserve the imported provider's source identity, quantified rows, shared anchors, effect/context payloads, and any role prerequisite.
- Keep `where` discharge type-directed and deferred until the exact receiver type and implementation member evidence exist.
- Verify ordinary imported uses and fail-closed identity cases without changing R149 source bytes.

R149, source/native correspondence, theorem closure, independent review, and production remain OPEN.

## R299 checkpoint: artifact ownership boundary

A fresh owner trace established the main integration constraint:

- `ConstraintBatch` owns exactly one `Arc<HirModule>` and constructs one term arena / collection artifact.
- `InferenceSession` owns that one batch. `FrozenInferenceData` and `CandidateSolvedResult` retain one HIR for later occurrence/root ownership checks and observations.
- `HirOccurrenceId` and `DefinitionRootId` are branded by a private `Arc<HirArtifactToken>`; `HirModule::owns_occurrence` and `owns_definition_root` require pointer identity. Flattening module item vectors or comparing ordinal/name alone would forge ownership.
- In contrast, `DefinitionUse` and candidate graph roots are already keyed by the artifact-branded `DefinitionRootId`, and collection assigns global dense ordinals. This provides a plausible same-session cross-module edge once collection can resolve an imported `SourceExportId` to the exact provider binding root.
- `resolve_source_export_owner` already verifies a public binding export against provider module path, source range, and parse-owned `SourceNodeKey`; R298 similarly authenticates the role implementation inventory.

No source code changed in R299. The smallest safe implementation direction is a candidate-only source-module world that retains each HIR artifact separately, builds one shared `ConstraintBatch`/term arena/session over the ordered module set, and routes every source/root/occurrence ownership query to its owning HIR. Imported names then become ordinary cross-module `DefinitionUse` edges; provider graphs remain in the same session and existing FreshUse route. The world must reject duplicate module providers and stale export owners before collection. The key acceptance test should use two independently lowered HIR artifacts and prove that the exact provider graph reaches two consumer uses without sharing their local FreshUse rows.

This is an implementation route derived from existing identity and session invariants, not a new language-semantic decision. R149 remains OPEN until provider and consumer source constraints, role discharge, output and runtime are connected.

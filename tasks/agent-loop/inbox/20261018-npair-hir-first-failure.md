# Frozen handoff: NPAIR HIR first-failure audit

Sprint-ID: `npair-source-admission-correspondence-20261018`, revision1,
contract SHA-256 `fdbc808bafb8d32df8f86701f41923fbaaf25de91764fdaf65429aa02da6ed25`.
Assignment-ID: `NPAIR-HIR-FIRST-FAILURE-20261018`; handoff revision1.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; all original
quantifiers/domain preserved; parent closure0.
Baseline supplied: `a5ac0942313e34fac178221a17a1501ed55bc6c2` (not Git-verified).
Author/worker: `/root/hir_first_failure_proof`; current session launch is the
primary's explicit NEW_TASK granting <=300s read-only proof lane.
Requested Sol/high; observed model/effort UNKNOWN/UNKNOWN. No descendants.

Outcome class: candidate source/native audit, not independently reviewed.
Artifact: `notes/theory/2026-10-18-npair-hir-first-failure.md`, SHA-256
`dd964fc6ed2c87ab2eb3d33ae583d1731d009ce6da58eee2d7b7fb2dee530542`.

Actual result: public StructuralProjection is lossy. It includes conversion of
FormationError::Unsupported at local_source.rs:36; it alone proves no identity
corruption or parser failure. First exact runtime producer remains UNKNOWN.
First direct source-key failure for a valid bare effect is declarations:198;
declaration shape/recovery can fail earlier with the same public result.
HIR constructors support unit type groups/unit expressions under their proper
CST shapes. Prior correspondence remains conditional on successful formation.
Existing producer fixture is useful design input, not successful execution.

Dependencies: all eight matching exact source hashes are listed in the note.
The frozen syntax read lease pins type_expr/mod.rs with ...59711f1464...;
actual owner is ...59711c1464... (full hashes in note). Read occurred before
validation; dependent parser findings withheld, primary notified. Stop boundary
is mismatch plus inability to identify the exact dynamic producer without a
new approved diagnostic. No hash silently corrected.

Source path: parse -> source-node map/effect declarations -> binding plan ->
LocalSource/formal annotation -> (unreached in failed fixture) source registration
and normal solve/preflight -> FormalAnnotation. No propagation/consumer/native
or provider/transport theorem follows.

Next step/TODO NPAIR-HIR-FIRST-PRODUCER-20261018: Luna reconciles parser pin and
authorizes the smallest discriminator of declaration recovery/shape/key vs
formal annotation vs body failure. Exact falsifier: first observed owner differs
from proposed cause. A fixture-only repair must retain the adopted negative row;
an identity repair requires its own owner-local contract. No semantic revision
requested by this evidence.

Checks/resources: source and SHA-256 inspection; no test/build/probe/Git/source
edit/external contact; full300s charged, actual CPU duration UNKNOWN; no scratch
paths. Exclusive written paths are artifact and this inbox only. Author cannot
independently certify combined evidence. Pending independent review/integration.
Writer STOPPED and writes stopped at frozen handoff; no unresolved descendants.

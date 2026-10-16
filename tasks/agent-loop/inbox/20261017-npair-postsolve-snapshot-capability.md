# Frozen post-solve capability proof handoff

Sprint-ID: `npair-postsolve-snapshot-capability-20261017`, contract revision 1.
Contract SHA-256: `3709fc3ee119b95583b2b92ce8c3aa7820e8ac8723b2f0441cc402b266433637`.
Assignment-ID: `NPAIR-POSTSOLVE-SNAPSHOT-CAPABILITY-20261017`; handoff revision 1.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.
Baseline supplied: `ac838c252a6567cd92c186ebf928348565e8004e`; no Git used.

Role/identity: leaf proof/source-audit producer,
`/root/npair_postsolve_snapshot_capability`, current-session, actual assignment
received from `/root` through collaboration. Requested `gpt-6-sol` / high;
observed model and effort UNKNOWN / UNKNOWN. No model-switch or independent
review claim. Sole author; no contributing descendants or delegated leases.

Exact leased/new/written paths:

- `notes/theory/2026-10-17-npair-postsolve-snapshot-capability.md`
- `tasks/agent-loop/inbox/20261017-npair-postsolve-snapshot-capability.md`

No scratch/generated paths. No other files written.

Outcome class: candidate source/native audit and conditional owner-capability
construction; exact storage blocker, not a source-qualified counterexample to
the parent and not a reviewed theorem.

## Main blocker and application

The successful returned result drops the actual physical lane arrays.
`InferenceSession::bounds/effect_bounds` (`lib.rs:7682+`) supply the eight
`VariableBounds`/`EffectBounds` lanes (`:4036+`). Neither the full
`FrozenInferenceData` declaration (`:7554+`) nor its construction in consuming
`finish_observations` (`:17749+`) retains them. They are read for projections
(`:17516+`) and destroyed with untransferred session fields. The test resource
branch explicitly drops them (`:17685+`), but ordinary omission suffices.
`CandidateSolvedResult` (`:7596+`) and `CandidateInference` retain only this
returned data. Captured `Graph::bounds` and retained `PhysicalBoundSlot`
descriptors are not the original physical lane storage. No read-only accessor
over this result can check the requested original row/lane/index/operand.

Parent application: the one-shot structural suffix still lacks the enforced
complete physical snapshot premise. A same-result owner check and the local
representative audit do not supply it. Parent/production remain OPEN;
implementation-readiness remains BLOCKED pending Luna's ownership decision.
No source-domain narrowing, semantics, bypass, `eta_op`, `realization_op`,
adopted `At`, source admission, subtraction, N-Transport or receive consumer
follows. Preserve F1/FK1 and other independent quantifiers and lineages.

## Relevant evidence and remaining qualifications

Source lifecycle: `CandidateInference::solve_mode` → consuming
`InferenceSession::run_candidate` → `execute` → consuming `finish_candidate`
→ consuming `finish_observations` → retained `FrozenInferenceData`.
Successful return can retain conflicts; graph export/fresh-use explicitly
refuse them. No executable source-construction evidence was produced.

New exact intrusion audit: `value_rep/effect_rep` call a shared slice walk
without path compression; ordinary forests and evidence changes require
exclusive state/session access. The prior transitive representative-read
uncertainty is resolved locally. Returned wrapper observers expose shared
access and no session continuation, but no universal transitive immutable-data
or completed-replay/restoration theorem is claimed for unpinned owners.

Conditional same-owner construction: privately minted handles retain a shared
reference to the actual non-zero-sized result owner; every combining resolver
checks reference identity, or resolves solely through that retained owner.
Shared references prevent moving/destroying an owner during later handle use;
two simultaneously live owners cannot be authenticated by lifetime/ID/HIR
equality alone. No such new API is implemented.

OwnerEmission/ExtrusionLink processing/ordinary-seed antecedents and FreshUse
Replay antecedents remain explicitly unavailable under
`candidate_context::BoundEvidence::admit`; iteration/ownership cannot clear
those gaps. Full completed-continuation/quiescence evidence remains unproved.
The physical-storage blocker was the exact assignment stop condition.

Reuse: prior proof by `/root/npair_snapshot_borrow_enumeration` only within its
conditional shared-borrow/evidence/accounting premises; Luna's revised
owner-interface obstruction and prior review disposition. Rejected: captured
graph as physical storage, solve success as source success, lifetime as owner
brand, and enumeration as authentication. Native source authors/settings are
UNKNOWN here. This producer cannot independently certify the combined result.

## Frozen artifact and dependencies

Theory artifact SHA-256:
`9e1ae6e71f095b89b09796e5da375d1f152427b658b6fe3bc045553632a4a3d6`.
Its direct-dependency table freezes the contract, all six allowed source
owners and all three prior artifacts. All ten hashes were actually checked
and matched before reliance. Source pins in compact order:

- `lib.rs`: `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`
- `candidate_intrusion.rs`: `7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c`
- `candidate_context.rs`: `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6`
- `candidate_effect.rs`: `11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb`
- `candidate_scheme.rs`: `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a`
- `shadow_apply.rs`: `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`

The frozen handoff's own actual byte hash is sent in the final collaboration
receipt, avoiding a self-referential hash. This ID/revision/hash is immutable
for Luna intake; subsequent changes require a new authorized revision.

## Mutual TODOs and stop receipt

`NPAIR-POSTSOLVE-PHYSICAL-RETENTION-20261017`: Luna with
`InferenceSession::finish_observations`, `FrozenInferenceData`,
`CandidateSolvedResult`, `CandidateInference` ownership. First missing evidence:
reviewed retention/ownership of the original physical lane vectors, or an
explicit decision to acquire a snapshot before destruction. Proposed output:
unapplied API/ownership contract preserving original row ordinals, lanes,
associations and an owner-checked quiescence condition. Falsifier: an alleged
live physical-slot resolver reads only descriptors/captured graph/reconstructed
relations, or omits row-kind/lane/index/actual-operand checks. No code lease.

`NPAIR-POSTSOLVE-EVIDENCE-COMPLETENESS-20261017`: Luna and
`BoundEvidence::admit` / future validator owner retain missing antecedents as
explicit incomplete/reject outcomes. Falsifier: successful solve or full
enumeration clears unavailable antecedents without independent owner evidence.

Checks/resources: four bounded stages; static reads and SHA-256 checks only.
No tests/builds/probes/Cargo/source/compiler execution/Git/network/nested CLI,
production edits or children. First observed clock 2026-10-16 23:37:59 UTC;
theory freeze 23:39:46 UTC, measured interval 107s. Entry before the first clock
and final handoff/hash overhead are not separately measured; conservative
assignment charge 180s of the 300s cap, 120s unspent. No reallocation claimed.
Final clock/hash receipt reports the actual observed end time.

Writer STOP: after this handoff write, only read-only final hash/time receipt;
both leased files frozen, no descendants, no outstanding writers. Assignment
ends at the exact blocker. No continued computation or RUNNING claim while
awaiting Luna. Fresh review/integration pending; next step belongs to Luna's
boundary decision, not another leaf attempt under unchanged premises.

# Source Check provenance sprint review

Date: 2026-10-16  
Sprint: `source-check-provenance-20261016`, contract revision 1  
Contract SHA-256: `ee70f6ae3e0f8318c6c1dcbc7eb4f8248259a232bd58f37cec228059762c81c4`  
Baseline: `eeb7826a238848d219058f4f14e0948c115ae6ac`

## Outcome

The original Apply/Check provenance audit was independently reviewed CLEAN by a fresh compiler referee. All 26 direct contract dependency pins matched. The audit traces “A1 constrained to alpha” to typed-core §6's complete invocation constraint. It does not recover an inserted `Check(Value(alpha), Value(A1))`; the Function annotation check concerns its actual whole-value endpoints, while SOURCE-GENERALIZE and same-provider realization retain whole-domain and whole-observation obligations. This is a bounded provenance gap, not a semantic non-entailment proof or source-qualified counterexample.

The accepted atomic Result theorem maps an authenticated uniform `VIncl(alpha,A1)` check to the neutral native Result child. The required source predicate identity or a proof from the original coupled premises remains missing. Even if supplied, whole declared-support inclusion and contextual/scoped-flow obligations remain separate. `AM-MODEL-1`, `FIRST-RESULT-ADEQUACY`, `F1-FULL`, `FK1-FOREIGN`, implementation E2E, and production remain OPEN.

The proof note records that current `candidate_effect.rs` had a different hash from the pinned historical native-flow note. Current-source evidence was excluded from the result; no equivalence, correspondence, or regression claim follows from the discrepancy.

## Tooling repair

The optional `AGENTS.override.md` route in `tools/agent_sprint.py` now activates when the path exists or is a symlink. Directories and dangling symlinks therefore reach the existing `read_text()` validation and fail visibly instead of being silently omitted. Required `AGENTS.md` validation and the rest of the checker remain unchanged. The exact pre-P2 bytes are preserved at `tasks/agent-loop/history/20261016-entrypoint-checker-pre-p2.py`.

The implementation author ran `python3 tools/agent_sprint.py check` once; it passed. A fresh independent spec-auditor review found no blocking, major, or minor issue and confirmed the delta against the exact snapshot. The P2 is closed. No tests, builds, probes, or compiler edits ran.

## Frozen evidence

- Proof note: `notes/theory/2026-10-16-first-apply-check-provenance.md`, SHA-256 `3890c26e1d9e53b29d7e6168b0bc3253dbe36954411592362eeebaf070cb969c`.
- Proof handoff: `tasks/agent-loop/inbox/20261016-first-apply-check-provenance.md`, revision 1, SHA-256 `1e65a5de1c60bb1446518407deab5d0c30be763effb5fca2300a11fba6f24d7f`.
- Checker: `tools/agent_sprint.py`, SHA-256 `b519df4b80eb6bf978ed40594f1554c5352bbeeff6245e194077586a1c67aa67`.
- Exact pre-P2 snapshot: SHA-256 `74a3e0ef3d41b425e8e156cbeed0304ccf8ea21a33ac0a9b1a8c1f656f50c010`.
- Tooling handoff: `tasks/agent-loop/inbox/20261016-entrypoint-checker-p2-repair.md`, revision 1, SHA-256 `7647f372ea837f5bd70d6e11b430ce7d4213864e9bdb2db8d820a1f35007cc44`.

## Resources and next owner

Proof work is conservatively charged at the full 900-second lane cap. Implementation reported at most 180 seconds but exact active time is unavailable. Reviewer and primary coordination durations are UNKNOWN; aggregate residual is not certified. No budget from an ended sprint was transferred. Three historical UNKNOWN identities and the quarantined board lease remain unchanged. All current producers and reviewers stopped; outputs are frozen.

Next owner: Luna / original Apply–Check rule owner, `SCP-SOURCE-1 / AM-MODEL-1`. Required input is either an authentic original rule instance retaining the predicate `q` with its endpoints, direction, telescope and same-object meaning, or a derivation of uniform `VIncl(alpha,A1)` from the actual coupled source premises. Current inputs do not justify another finite-reflection attempt or a relabeled MODEL theorem.

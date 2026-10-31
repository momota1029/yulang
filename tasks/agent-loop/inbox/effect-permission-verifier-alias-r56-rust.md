# R56 Rust handoff — verifier alias relocation

Assignment: `EFFECT-PERMISSION-VERIFIER-ALIAS/20261031-R56`
Contract SHA-256: `5b37c703b982fd81b15ac527f3b3efb266f1e764b9cbd94091ea352a5fdc0b58`
Admission SHA-256: `bc598af39952b7b467e09879f86c15b832b7d10ef639cb8e11a963d841b2c074`
Requested model/effort: Luna/high. Observed model/effort: UNKNOWN.

## Exact change

Moved the existing `let permission = &self.internal_incidence.permission;` inside `SourceInternalProjection::verify_owner_round_trips` to immediately before its first use in the Function-child comparison and removed its later location. No other source change was made. B1's prior construction-block move and every selection/check remain unchanged.

## Rehashed inputs

- R56 contract `tasks/agent-loop/sprints/effect-permission-verifier-alias-20261031-r56.md`: `5b37c703b982fd81b15ac527f3b3efb266f1e764b9cbd94091ea352a5fdc0b58` (matches admission).
- R56 admission `tasks/agent-loop/history/effect-permission-verifier-alias-20261031-r56-admission.md`: `bc598af39952b7b467e09879f86c15b832b7d10ef639cb8e11a963d841b2c074`.
- B1-closed/B2-open receiver source baseline: `7b0698e6ac26ec1ba983d83006ef14d14a600b37e805ec0455120f24e2f6f224` (matched exactly before writing).
- R55 Rust handoff with rejected diff archive: `tasks/agent-loop/inbox/effect-permission-source-internal-r55-rust.md`, `db9e9a2fcd545502f501e103d40a66fa41343c7906e44efca4e1d72087f48b4f` (matched before writing).
- Read-only `candidate_effect.rs`: `75267bd1a195121ca79addb62b2a446a4b1b26afcc11e8c70aa1fa732c9e2909`.

## Checks and frozen output

- `git diff --check`: PASS.
- `python3 tools/agent_sprint.py check`: STATIC CHECK PASS; not execution or independent review.
- No build, tests, or type-check ran, per contract.
- Repaired `crates/yu-solver/src/candidate_receiver.rs`: SHA-256 `28594d25657ddafde5b97f7faa25f28285a6a20cca077bb0a974ca5c2558777f`.

Only the two leased paths were written. No scratch or disposable path was created; no Git mutation was performed.

STOP: the one-line relocation and permitted checks are complete. No further writes will be made in this assignment.

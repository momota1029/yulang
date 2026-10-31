# Sprint EFFECT-PERMISSION-VERIFIER-ALIAS / R56

Status: CANDIDATE pending primary admission. Fixed-gate lexical repair continuing the existing inference/effects objective. Same branch `yulang3`, same checkout; no new environment. Full Git baseline before R56 admission: `3f8d03f77004d3c8bf5c27b27e934479d0cff73d`.

## Exact outcome

Close R55 review finding B2 only. In `SourceInternalProjection::verify_owner_round_trips`, move the existing exact incidence permission alias

```rust
let permission = &self.internal_incidence.permission;
```

to immediately before its first use in the Function-child comparison and delete the later copy. Make no other source change. B1 is already closed and must remain closed. Preserve all selections, checks, fields, and outputs.

This packet does not expand R55 semantics, source domain, proof claim, or production authority. Reuse the accepted R55 Lean Audit6 only after the reviewer verifies that this alias relocation leaves reader meaning unchanged.

## Inputs and exact pins

- R55 incomplete outcome: `tasks/agent-loop/history/effect-permission-source-internal-context-20261031-r55-outcome.md` (hash recorded at admission).
- R55 final review report: `tasks/agent-loop/inbox/effect-permission-source-internal-r55-review.md` (hash recorded at admission).
- R55 Rust handoff contains the exact rejected receiver diff against immutable R54 baseline `cd914826f79cec065af2dbba7bb79d0ddc7681080e12a0e974738186118e769f`, rejected receiver hash `befdb77ea88becca357f83914f61ade7e09bf93bd33e5adb2ee017d0e51a76aa`, and B1-closed/B2-open source hash `7b0698e6ac26ec1ba983d83006ef14d14a600b37e805ec0455120f24e2f6f224`.
- R55 accepted Lean module: `7aaecdd3d358d769123f00acb4b19b4d7d61ccfef98fee4eb53179da4a105123`.
- Frozen R55 candidate-effect bytes, including pre-existing dirty baseline plus the reviewed iterator visibility delta: `75267bd1a195121ca79addb62b2a446a4b1b26afcc11e8c70aa1fa732c9e2909`. Read-only; no edits or staging of unrelated hunks.
- R56 source baseline is the exact B1-closed/B2-open file above. The full checkout baseline is the R56 admission commit, recorded separately; never substitute the RUNNING receipt commit for source-baseline evidence.

Any mismatch stops the packet before writing. The exact intended source delta is a single alias relocation. Any other byte change or unresolved verifier use is a blocker.

## Leases and budget

- Rust author `/root/r52_rust`, requested Luna/high, at most 120 seconds: `crates/yu-solver/src/candidate_receiver.rs` and `tasks/agent-loop/inbox/effect-permission-verifier-alias-r56-rust.md` only.
- Fresh non-author reviewer `/root/r48_review`, at most 240 seconds, read-only; report path `tasks/agent-loop/inbox/effect-permission-verifier-alias-r56-review.md` is owned by primary.
- Primary at most 840 seconds including 500 seconds closeout.
- Total envelope 1,200 seconds. No R55 budget transfer, no Astra, and no new prover assignment.

Reviewer must verify the exact insertion/deletion, binding availability before every use, B1 still closed, no changed selection/check, source hash/delta isolation, and that R55 Lean evidence remains applicable. Any changed reader meaning returns the gate to proof review.

## Verification and Git

Only `git diff --check` and `python3 tools/agent_sprint.py check` are allowed. No build, test, type-check, Cargo, Lake build, formatter, environment/worktree, cache, scratch, service, nested CLI, or persistent process.

After author STOP and independent PASS, primary stages only the reviewed receiver delta, R56 handoff/review/outcome/admission/current-state records, plus explicitly reviewed R55 source contribution hunks. Preserve the pre-existing `candidate_effect.rs` changes and every unrelated dirty path. Inspect the complete outgoing range, then commit and push the coherent reviewed checkpoint to `origin/yulang3`.

Full R48/R49 candidate extraction, runtime, complete Context/R50, R51 primitives, parent A/B, soundness, principality, termination, full hygiene, and production remain OPEN.

# R56 admission — EFFECT-PERMISSION-VERIFIER-ALIAS / 20261031-R56

Primary admission under the standing ongoing objective, after dispatcher recommendation. R55 is closed incomplete with B1 closed and B2 still blocking. The exact rejected R55 receiver and delta are preserved in its Rust handoff; no R55 source checkpoint was accepted.

Full Git baseline before R56 admission: `3f8d03f77004d3c8bf5c27b27e934479d0cff73d`. This records repository state only; the source-specific R56 baseline remains the exact B1-closed/B2-open receiver hash below.

## Scope and leases

Only one change is admitted: move the existing incidence-permission alias inside `SourceInternalProjection::verify_owner_round_trips` immediately before first use and remove its later copy. No semantic, source-selection, proof, API, or producer changes.

- Rust author `/root/r52_rust`: `candidate_receiver.rs` plus R56 Rust handoff only; max 120 seconds.
- Fresh non-author reviewer `/root/r48_review`: read-only review, max 240 seconds.
- Primary `/root`: contract/admission/outcome/current state and review placement; max 840 seconds including closeout.
- Total 1,200 seconds; no budget transfer from R55.

Read-only pins: R55 Lean module `7aaecdd3d358d769123f00acb4b19b4d7d61ccfef98fee4eb53179da4a105123`; candidate_effect `75267bd1a195121ca79addb62b2a446a4b1b26afcc11e8c70aa1fa732c9e2909`; B1-closed/B2-open receiver baseline `7b0698e6ac26ec1ba983d83006ef14d14a600b37e805ec0455120f24e2f6f224`; rejected receiver `befdb77ea88becca357f83914f61ade7e09bf93bd33e5adb2ee017d0e51a76aa` and R54 baseline `cd914826f79cec065af2dbba7bb79d0ddc7681080e12a0e974738186118e769f` preserved in R55 handoff.

## Admission checks

- Live roster: prior R55 Rust author and reviewer both STOPPED; no active writer remains on the source lease.
- Unknown workers and quarantined paths are unchanged; no lease was released or inferred stopped.
- The R56 exact source lease is newly assigned after the stopped R55 attempt. Candidate-effect and Lean paths remain read-only.
- No tests/build/type-check, environment, cache, scratch, worktree, or service is authorized.
- Required pre-write rehash: contract pins and exact B1-closed/B2-open source baseline. Stop on any mismatch.

## Gate

R56 succeeds only after the single alias relocation is independently reviewed and B1/B2 are both closed. The prior Lean audit remains in scope only if the reviewer confirms no reader meaning changed. Full extraction and parent obligations remain OPEN.

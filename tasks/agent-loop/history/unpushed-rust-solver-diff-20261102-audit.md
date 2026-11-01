# Read-only audit of unpushed Rust solver changes

Primary intake of the independent static review returned by
`/root/rust_dirty_diff_review`. Reviewer-reported response hash:
`adf7ab01717976fa1240f37bc540623f7f6d0de195b136c4403ba503744ccece`.

## Frozen target and disposition

Base: `225c5519943fc490c3d5620683918674f4f6afd5`.
The exact three-file `git diff --binary` for `candidate_effect.rs`,
`candidate_scheme.rs`, and `shadow_apply.rs` had SHA-256
`643d75e8e8435253a8606af7800134c28ce8eb74c86b1880ab169d5b8891bd1a` at both
the review's start and end.

Disposition: **HOLD** the entire three-file diff as a safe research checkpoint.
The reviewer found one major session-identity boundary regression. This is not
a demonstrated production typing regression; compilation, excluded callers,
runtime behavior, and theorem closure remain unverified.

## Major finding

`candidate_scheme.rs:505–535` replaces a session-owned permission binder with
independently supplied route, store, effect state, and registered formals. The
current code checks source IDs and session-local numeric registration/row
ordinals, but the compared `definition_use` and `context_use` fields are
constructed from the same route and therefore do not prove that the supplied
effect state belongs to that route's inference session. `candidate_effect.rs`
authenticates the permission against the supplied registration, not against the
route's owning inference state.

A route and arena from session A can therefore be combined with effect state and
registrations from session B when both were lowered from the same source and
retain equal IDs/ordinals. The resulting permission-use record can combine B's
permission with A's FreshUse map. The previous session-owned wrapper prevented
this join. The minimum repair is to retain that wrapper or provide an unforgeable
shared owner/brand and reject cross-session joins, while justifying each removed
source/native check at its owning constructor. Do not restore
provider-equals-source-owner indiscriminately; returned/local functions can have
a distinct constructor owner.

Most additions are `cfg(test)` trace/fixture support. The diff also changes a
non-test binder API/validation and retains raw `entry_effect` through capture
and freshening, so it is not instrumentation alone. The added tests were not
run and their assertions are not accepted as passing evidence.

## Exclusions

The independent reviewer did not inspect `candidate_receiver.rs` or quarantined
runtime files. Separate primary inspection found that the dirty
`candidate_receiver.rs` diff deletes owner/batch/live-state identity checks,
provider/arm identity checks, and exact permission-origin matching; that file is
also excluded from any push. Runtime `machine.rs` and `receiving.rs` remain
quarantined to `UNKNOWN_WRITER` and were not read.

No Rust diff in this audit is committed or pushed. No builds, tests, Lean, or
execution ran. The narrow R151 source trace is separately committed as
research-only evidence; it does not repair this session-identity regression.

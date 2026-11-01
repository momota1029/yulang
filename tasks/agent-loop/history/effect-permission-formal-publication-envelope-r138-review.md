# R138 independent source review — PASS

Assignment: `R138-PUBLICATION-OWNER-REVIEW-1`
Reviewer: `/root/r138_source_review`
Submission revision: `R138-PRODUCTION-FAILURE-ENVELOPE-SOURCE` / 1
Baseline: `4c1d58a646a1101c080659ebfed6ae7862d8aded`

Reviewed submission SHA-256: `0f154a69453984dd665b6994f4eb1be0c8cdfa45cdd9d6433bb1eafa8f1cb18d`
Verified submission size: 13,514 bytes.

## Verdict and governing invariant

**PASS for the bounded failed-session discard envelope. No BLOCKING, major, or minor correctness findings.**

Authoritative `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§4–5 permits termination and discard of an affected private attempt without complete internal restoration, provided inconsistent partial results do not escape.

The constructors do not restore their published permissions on every `Err`. The supported production callers inspected here prevent those failures from producing a returned candidate or reusable session. This establishes discard at the owning boundary, not constructor atomicity or universal rollback.

## Independently traced evidence

- `candidate_effect.rs:1819–1831`: outer entry permission publication precedes the fallible resource sample.
- `candidate_effect.rs:1950–1976`: nested permissions and formal domains are published before the fallible sample and scratch cleanup.
- `candidate_source.rs:2358–2367,2459–2475`: direct action dispatch propagates failure before cursor advancement; synchronous cleanup removes the source frame without restoring permission fields.
- `candidate_scheme.rs:3083–3121,3218–3221,3374–3386`: definition roots, member schedules, and operator-provider expression schedules propagate failures with `?`.
- `lib.rs:10702–10729,17178–17187`: SCC, loose, and expression schedule failures propagate to the owning solve; accounting cleanup does not restore permissions.
- `shadow_apply.rs:1833–1932`: both ordinary and deferred-readback solve branches own the session locally. Failure paths return without constructing `CandidateInference`; successful paths consume the session through `finish_candidate`.
- `candidate_receiver.rs:3158–3180,5550–5675`: receiving action failures and later assembly failures discard the local session. Residual-publication failure discards the local experiment before its return.
- `candidate_receiver.rs:3183–3249`: publication can fail after some forwarding mutations; those mutations remain private to the experiment discarded by its caller.
- `lib.rs:7933`, `shadow_apply.rs:508–509`, and `candidate_receiver.rs:21–28`: session ownership is private. Crate-external callers cannot retain or resume the failed session through these public result types.

### Catch-and-continue challenge

`shadow_apply.rs:1619–1635` is a relevant alternate public owner: it catches `DeferredSelectionUnavailable` and can return `Ok(readbacks)` after an inner solve fails.

This does **not** falsify the reviewed envelope. Its returned data consists of diagnostic readbacks; it does not return the session, `CandidateInference`, or permission-bearing graph. The post-publication constructor failures examined here propagate as resource failures rather than this accepted deferred outcome.

Internal capture and lambda-domain consumers can execute during a solve before its final completion. Their products remain within the private attempt. The justified conclusion is that **external permission-bearing candidate consumers receive only a successfully returned candidate**, rather than a claim that every internal consumer runs after final success.

### Rollback and tests

`candidate_effect.rs:502–535`, `candidate_intrusion.rs:177–202`, and `lib.rs:9546–9610,9711–9769` confirm that route journaling can restore permission fields. The production formal-action schedule does not obtain that encompassing transaction.

Relevant committed tests, including failure injection around `candidate_effect.rs:3674–3692`, explicitly wrap constructors in route transactions. Those wrappers were not treated as evidence of production rollback.

## Verified source SHA-256 values

| Source under `crates/yu-solver/src/` | SHA-256 |
|---|---|
| `candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `candidate_effect.rs` | `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01` |
| `candidate_scheme.rs` | `e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814` |
| `lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `shadow_apply.rs` | `2fa42a5570e660babab5da6361e0d71e0c022b234a21f7e01b78eafbfc65f278` |
| `candidate_receiver.rs` | `335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165` |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |

All seven match the submission.

## Coverage, checks, and limits

Read-only committed call-site searches covered constructor calls, source-action dispatch, schedule drivers, candidate initialization, session execution/finalization, member and provider schedules, feature gates, and public ownership boundaries. Archived snapshot search hits were excluded from evidence. No supported production caller retaining a failed permission-bearing session was found.

Checks used immutable `git show`/`git grep` and in-memory SHA-256 calculation. The initial hash command used unavailable `python`; the equivalent `python3` command succeeded.

No files were modified. No Git mutation, status, dirty diff, build, test execution, Lean execution, scratch output, or delegation occurred. No new runtime or theorem evidence is claimed.

Resource envelope: one reviewer; 240-second assignment cap; CPU/RSS and exact elapsed time not instrumented.

This receipt supports applying the bounded envelope to `R137-PUBLICATION-ROLLBACK-1`. It does not close source/native inventory equality, source-to-Lean identity correspondence, `SourceProblem.InferenceSoundness`, effect-hygiene H, or production approval.

Worker state: **STOPPED**. No descendants; no output files written.

# R31 stage ledger

The local admission is synchronized in `current.json`; its remote checkpoint is
unpublished. A worker may start only after its exact leases are transferred to
its identity and live launch is recorded. Use the existing checkout. No project
copy, worktree, target, cache, Cargo, or Lake.

## Luna pre-admission source preparation

Read the exact R29 runtime failure and streamed R30 archive, then prepared the
one-assertion typed-identity patch and source mapping in the two Rust output
paths below. This is a primary draft, not a worker completion, independent
review, compile, test, or runtime result. Rust and Lean drafts were transferred
into exact worker leases after source freeze, and both registered workers are
live; review remains deferred. The earlier intake/source-read interval was not
instrumented, so remaining primary seconds are not asserted until the
admission/resource receipt is reconciled.

| Stage | Owner | Exact paths | Initial state | Gate |
|---|---|---|---|---|
| Rust correspondence proposal | `/root/effect_permission_r31_rust` | `tasks/agent-loop/artifacts/native-callback-grant-r31.patch`; `tasks/agent-loop/inbox/effect-permission-native-callback-grant-r31-rust.md` | NOT_STARTED | Freeze patch and source mapping; no runtime source edits |
| Lean projection and audit | `/root/effect_permission_r31_lean` | `notes/theory/lean/YulangClosure/NativeCallbackGrantBridgeR31.lean`; `tasks/agent-loop/inbox/effect-permission-native-callback-grant-r31-proof.md` | NOT_STARTED | Pinned Lean stdin audit, checks for every declaration, complete `#print axioms`, no writes |
| Independent review | `/root/effect_permission_r31_review` | `tasks/agent-loop/inbox/effect-permission-native-callback-grant-r31-review.md` | DEFERRED | Starts only on frozen Rust and Lean outputs |
| Luna primary | `/root` | R31 contract, manifest, admission, ledger, current state, closeout | ACTIVE | Exact leases, receipt synchronization, adjudication, explicit staging, commit and push |

## Live dispatch receipt

At 2026-10-30 16:28 UTC, the synchronized collaboration roster confirmed
`/root/effect_permission_r31_rust` and `/root/effect_permission_r31_lean` as
RUNNING in session `R31-20261030`. Rust owns only the patch and Rust handoff;
Lean owns only the standalone module and proof handoff. No review child is
running; its exact path remains primary-held until both outputs freeze.

Resource envelope: 6,000 seconds total (Rust 1,600; Lean 1,600; independent
review 1,200; Luna primary 1,600 including 500 closeout reserve; Astra 0).
R30 seconds do not transfer. The original source-preservation A/B and all
broader semantic and production claims remain OPEN.


## Runtime reconciliation — 2026-10-30 16:32 UTC

The live collaboration roster showed Rust terminal with a frozen source-only proposal and Lean terminal with no output; no descendants remained. Rust output hashes are recorded in its handoff. It did not modify runtime source or run a compiler, test, or runtime. Lean verified archive/member hashes and the pinned Lean version, but `strace` exited 1 at `PTRACE_TRACEME: Operation not permitted` before Lean started. No R31 module, theorem type, or axiom audit was produced. Both workers have stopped writing. Rust artifact leases are frozen; the empty Lean output leases returned to Luna. Resource durations were not instrumented and are not reset or claimed as remaining.

A read-only `bwrap --ro-bind / / --dev /dev --proc /proc <pinned-lean> --version` check succeeded at Lean 4.35.0. This provides a no-write execution boundary for a resumed stdin audit; it does not capture attempted syscalls. Next action is to continue the same Lean packet using that boundary, still with no Lake, Cargo, project copy, target, or cache.


## Lean continuation lease transfer — 2026-10-30 16:32 UTC

After confirmed write cessation and no descendants, Luna transferred only the two exact empty Lean output leases back to `/root/effect_permission_r31_lean` for continuation of the same packet. The existing 1,600-second assignment cap is unchanged; no fresh budget or prior-time reset is claimed. A read-only bubblewrap invocation of the pinned Lean binary succeeded for `--version`. Live RUNNING status will be recorded only after the continuation is actually observed.


## Lean continuation live receipt — 2026-10-30 16:33 UTC

The live collaboration roster confirmed `/root/effect_permission_r31_lean` RUNNING after Luna's follow-up. The same two exact Lean leases remain exclusive to that worker. The task continues within the original 1,600-second cap; prior and current active duration remain uninstrumented, with no fresh allocation or reset. The worker will construct the standalone source, then run only the pinned Lean executable with stdin inside the verified read-only bubblewrap namespace. No project copy, Lake, Cargo, target, cache, or log file is authorized.


## Frozen Lean result and review lease — 2026-10-30 16:34 UTC

The live roster confirmed the Lean worker's final message and STOPPED receipt; no descendants remained. Frozen revision 1 hashes: standalone module `a0a8b53e1f73ed44e92ee01b3e87531d310775af0804999d30d6fbb0a68e378d`; proof handoff `8c8864cfcd5a93deb66caf6c6c62c5d4078d469c136b75bc559f2ed1ee767732`. Read-only bwrap stdin audit on pinned Lean 4.35.0 exited 0 in 5.696 seconds with empty stderr; all 30 R26/new declarations' types and complete axiom outputs are captured in the handoff. The new eight laws cover finite index round-trip/injectivity, structural operation mapping, family-membership correspondence, UseReady reconstruction, and conditional checked-Catch composition. Axioms are `[propext, Quot.sound]` except `callback_use_ready`, which has none. Concrete native identity extraction, table coverage, Grant/request provenance, and native History remain OPEN; no Rust source or runtime was changed. The earlier `strace` attempt failed before Lean; bwrap prevents ordinary filesystem writes but does not capture attempted syscalls.

The frozen Rust proposal/handoff remain at hashes `4eb744c6aec78d15c98724d6559440de3a477c1e67ec1116b6eee89ce38a6f85` and `3e1fbe2fabc5869feaad573453fa7bff8b463fa04cddd95e7ff2d27f8703596d`. R29's three STOPPED worker observations are retained in the authenticated admission record; their resolved current-state worker rows are now archived out of the compact live snapshot. Luna transferred only the review output lease to `/root/effect_permission_r31_review`; the reviewer starts after live launch synchronization.


## Independent review live receipt — 2026-10-30 16:38 UTC

Live collaboration roster confirmed fresh reviewer `/root/effect_permission_r31_review` RUNNING. Requested `compiler_referee`/gpt-6.1-sol medium; observed model/effort UNKNOWN. Its sole exact lease is `tasks/agent-loop/inbox/effect-permission-native-callback-grant-r31-review.md`. Inputs are the four frozen R31 artifacts and pinned R31 contract/manifest. Reviewer has no authority to edit them, run Cargo/Lake, or create build/cache/copy/log/scratch outputs. Review budget cap is 1,200 seconds.


## Independent review disposition and incomplete closeout — 2026-10-30 16:42 UTC

Reviewer final message was returned via the read-only role; Luna preserved its independent finding in `tasks/agent-loop/inbox/effect-permission-native-callback-grant-r31-review.md` (SHA-256 `d8e095ba4e9731478549912079ac60023556a6f89801bbd6e36915a67e6bd7f5`). The frozen pair fails the faithful-projection gate with `PROJECTION_COVERAGE_GAP`; no invalid Lean proof or native typed-ID collision was found. The R31 result is CLOSED_INCOMPLETE. Rust proposal and finite conditional Lean mathematics are retained as partial evidence. No R31 Rust/Lean/review allocation is transferred to a successor: Rust, Lean and primary preparation intervals were unmeasured; reviewer active time is also UNKNOWN. No R1 artifact was changed after review.

The next bounded action must be admitted separately with a fresh resource envelope and the table-coverage counterexample fixed; it must require and use operation-table membership, full family-row coverage, operation round-trip, and covered family-membership equivalence. No compiler runtime source edit or Cargo run occurred in R31.

# R104 outcome

Status: `LEAN_GATE_PASS; RUST_FINAL_GATE_FAILED; RECEIPT_REVIEW_PASS; CLOSED`.
Contract: `tasks/agent-loop/sprints/effect-permission-source-causality-20261101-r104-v3.md`.
Admission: `tasks/agent-loop/history/effect-permission-source-causality-20261101-r104-admission.md`.
Amendment: `tasks/agent-loop/sprints/effect-permission-source-causality-20261101-r104-v2.md`.

## Lean bounded gate

Candidate `SourceLogicalOccurrencesR104.lean` is 23,908 bytes, SHA-256
`0e7a42d66578388585a5abd1da12c77a9d7d46823687ed511d26e359b3078f39`;
handoff is 12,979 bytes, SHA-256
`5f9440ec72b2dbd058b2e3975040ec10ecf1778ceb9e116d9b7ab724c3efdef7`.
Fresh static review passed before execution. The exact flattened input was
112,345 bytes, SHA-256
`e5c6d9f734bb648c4280a2307243a2f74e3015bd02fd73910710e4dad298a85e`.

One invocation used the pinned Lean 4.35.0 binary
`bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38` with
`--stdin -j1 -M1024`, `timeout -k 5s 120s`, and CPU affinity 0. Timed exit 0;
elapsed 15.63 seconds, maximum RSS 902,132 KiB, swaps 0. Stdout: 9,929 bytes,
SHA-256 `f9dec1837a59b1d60aa0d1af18e2e441d128a02b36bc7ede245f1d42e1b99a10`.
Stderr: 826 bytes, SHA-256
`9be652d6633cb1dd98eb474a879da1b887c161dc07c9de025da65ff9e5b1d414`.
All ten theorem headers/types and full axiom lists were emitted. No `sorryAx`
or project axiom appears; dependencies are only `propext`, `Classical.choice`,
and `Quot.sound`. The only diagnostic is the inherited unused `Prod.exists`
simp-argument warning. A fresh receipt reviewer passed. Outer shell success is
derived from the recorded timed exit 0 and the `pipefail` wrapper; the shell
metadata itself was not retained independently. There was no retry.

This closes only the bounded flattened syntax theorem gate. Module import/build,
source-owner and logical-admission correspondence, the original lawful joint
strategy, effect hygiene, source/native correspondence, A/B and production
remain open. The first bridge is recorded in the proof handoff.

## Rust pre-execution review

No Cargo invocation was made. Frozen Stage-1 candidate hashes:

| File | SHA-256 |
| --- | --- |
| `candidate_effect.rs` | `0e6f11d4c9b310e1d18952cdf17dea7b48b64ce30cb7421ecf28524bcfd59023` |
| `candidate_scheme.rs` | `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470` |
| `candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |

The fresh compiler-referee rejected the candidate for the bounded observation
command on three findings:

1. `candidate_effect.rs:2735` accesses `row.position` in the `else` arm of
   `let Some(row) = row else`; there `row` remains an `Option`, so the test
   target does not compile. The suggested test-only correction is to record the
   existing `context.position()` while preserving the no-source-row fact.
2. Per-route Support output reports template nodes/rows but omits the retained
   `effect_operands` crosswalk and actual fresh-use remap. It cannot distinguish
   missing Support at capture from a later remapping loss.
3. The contract command hides captured output from passing tests, so required
   successful observation output would be absent from saved logs. A harness
   setting must be explicitly authorized before the bounded invocation.

Reviewer verified the four candidate hashes and protected `r != q` assertion;
no Cargo, build, test, edit or Git operation occurred. The source writer held
the frozen files until Luna's versioned R104 v2 thaw. R104 v2 keeps the same
owners and two-call/resource envelope, requires the no-row and Support-remap
observation repairs, and authorizes `--show-output` solely to retain
successful-test logs. The two-call Rust allowance remains unused. No Rust
source integration is accepted or pushed.

## Overall disposition

Lean proof artifacts and logs form an independently reviewed checkpoint; they
do not close the parent theorem or authorize Rust promotion. Rust source remains
unintegrated until the authorized execution and receipt gates pass. All original
R102/R103 failures and UNKNOWN/quarantined leases remain intact.

## R104 v2 Cargo call 1/2

The reviewed command was run exactly once with the v2 `--show-output` flag,
locked/offline, CPU affinity 0, 180-second timeout and the unique authorized
`/dev/shm/yulang-effect-permission-source-causality-20261101-r104-target`.
Cargo failed before tests with exit 101. `candidate_effect.rs:3618` tried to
format `CandidateGraphEffectOperand` with `Debug`; that enum in read-only
`shadow_apply.rs` has no `Debug` implementation. No test ran.

Complete stdout is 0 bytes, SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`. Complete
stderr is 27,612 bytes, SHA-256
`70cdafc05b6f98774466d8b5bee8d8d1afa0564de83df3d12bf9bc6648034481`; it
contains the full compiler error, warnings and GNU time receipt. Elapsed time
73.13 seconds, maximum RSS 1,211,796 KiB, zero swaps; measured CPU 82%. The
target directory is absent after command completion. No retry occurred.

The fresh dispatcher recommended a test-only explicit-field formatter inside
the existing effect lease, not a `Debug` derive in a read-only owner. R104 v3
is admitted: Cargo call 2/2 is the sole final corrected causal-observation
invocation after a fresh independent review; it is consumed regardless of
result. No later Rust command or solver-repair verification is allowed in this
sprint. Exact amendment and admission are linked in the current sprint record.

## R104 v2 revision 2 review

Following the first v2 rejection, Luna accepted the in-scope direct-row bounds
gap and thawed only the existing Rust owners and handoff. The source writer
added direct lower/upper row bounds, both atom lanes, representative identities,
reverse direct-row references and explicit unavailable-versus-empty states.
The captured original tail is now distinct from the expected mapped tail.

Frozen source hashes:

| File | SHA-256 |
| --- | --- |
| `candidate_effect.rs` | `4c8dd62be1329a61437adabf9c340e9122888694632e25345815508e82949619` |
| `candidate_scheme.rs` | `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470` |
| `candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |

The final handoff is sequential revision 3, SHA-256
`4d4504ab88a462d634e6151b60a189f248e960ab7979df7e26b5fc85d05f7629`.
It corrects the stale `candidate_effect.rs` hash and records review disposition;
Luna acknowledges this exact frozen artifact. The fresh compiler-referee passed
the observation candidate after all source findings were closed. One remaining
finding was solely the stale handoff hash; after sequential correction the
reviewer confirmed the four source hashes were unchanged and that no source
rereview was needed. At that review point Cargo was 0/2; the later first-call
failure is recorded above.

The sole permitted stage-1 invocation is:

```sh
cargo test --locked --offline -p yu-solver --features shadow-apply-candidate candidate_effect::tests:: -- --test-threads=1 --show-output
```

It uses only the unique authorized `/dev/shm/yulang-effect-permission-source-causality-20261101-r104-target`; do not persist a target or cache. Source promotion still requires the bounded test result and a fresh independent receipt review.

## R104 v3 final-call candidate review

After the v2 pre-test compiler failure, the formatter was changed to print
Support fields explicitly, exhaustively render origin variants, and resolve
tail-node identity without adding a `Debug` derive or editing a read-only owner.
R104 v3 admitted this as the sole final Cargo call after independent review.

| File | SHA-256 |
| --- | --- |
| `candidate_effect.rs` | `fab53f41cba94da6ada8850ae99b4ab03a7bfce46ff8f71306dc1b77ade73cb5` |
| `candidate_scheme.rs` | `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470` |
| `candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |

Handoff revision 4 SHA-256:
`4a4227fb6ca8cbefa3240cbec4b4fd485f3583750816827338b0717e0dfed5d5`.
The fresh compiler-referee passed the formatter delta and full observation
component for final call 2/2. It confirmed the no-row and explicit-output
repairs, source/capture/remap/direct-bound traces, protected assertions, and
unchanged fixtures. This was execution approval only; no solver result or Rust
source promotion was implied.

## R104 v3 final Cargo call 2/2 and receipt review

The sole final command matched the reviewed v3 candidate and exact authorized
locked/offline command, with `--show-output`, CPU 0, 180-second timeout and the
unique `/dev/shm/yulang-effect-permission-source-causality-20261101-r104-target`.
It exited 101 from ordinary protected test failures, not compilation or timeout.
The selected tests reported 47 passed, 4 failed, 2 ignored and 771 filtered.
GNU time was 98.91 seconds, wrapper time 99.02 seconds, peak RSS 1,727,936 KiB,
zero swaps, and target peak 4,415,128,655 bytes. Cleanup was complete; the
independent reviewer confirmed the target absent and no Cargo, rustc or test
process remaining.

Complete stdout (682,262 bytes) SHA-256:
`46a2b246f1aa1b44704f443020ed6e4a08c20b6ec23f2ebcc5f2c3252e68861d`
Complete stderr (33,992 bytes) SHA-256:
`8146cae5ab7e6d1e37e2095d551e94a810eacb0fb4807185ba265bee0a35836e`.
Target peak record (449 bytes) SHA-256:
`7daa47185588a2f80305a62d08237bfd4a3e59b8ea19ef0f8656c288e883faf2`.
The fresh final receipt reviewer passed the hashes, command, resource/cleanup
receipt and required observations. It did not approve source promotion.

Observed causal results, with protected assertions and fixtures preserved:

1. The shared-tail `IncompatibleValue { lower: Int, upper: Function }` at
   occurrence ordinal 2 / slot 40 already exists after root execution. Late
   `E` at slot 61 returns `Ok(0)` and adds no error (stdout lines 4712–4720).
2. The unequal-transport run reports identity representatives and
   `parent_events=[]`; the assertion requiring `r != q` still fails on
   `[(21,21),(23,23)]` (stdout line 4728). This run supplies no unequal
   transport and therefore does not establish canonicalization loss.
3. A separate returning-pair provider produces an operation-origin Support
   node and zero conflicts, while the original recursive consumer reports no
   returned effect forms and fails its retained expectation (stdout lines 1823,
   7347). The separate fixture does not discharge the original consumer test.
4. Both fresh-route templates have no captured Support node despite a live
   Support row and distinct retained Allowances (stdout lines 7353–7355). This
   locates absence in the captured templates; it does not demonstrate loss in
   Support remapping. The protected `.all` assertion remains failing.

The four protected failures remain at `candidate_effect.rs:4986`, `:3920`,
`:3943`, and `:5807`. Assertions later in those tests were not reached and are
not claimed verified. This closes only the R104 causal-observation packet.
Keep the Rust candidate and handoff unintegrated; no solver change or test
promotion follows from these logs. The Lean result remains the separately
reviewed bounded flattened syntax gate, not module-import, parent theorem,
source-owner correspondence, source/native, A/B, or production closure.

## Sprint-end selection

The registered `next_action_selector` recommended closing R104 with the Lean
bounded gate passed and Rust source promotion failed. It identified a
hypothesis for independent source-contract adjudication: `candidate_source.rs`
applies a named header annotation to the terminal body, while the shared-tail
fixture returns `pure : int → int` with a result annotation shaped as
`(int → int) → (int → int)`. The observed `Int ≤ Function` edge could be
consistent with an extra function layer in that fixture. This is a hypothesis,
not a semantic finding or approved behavior change.

The proposed R105 Rust outcome is to classify all four protected failures
against the named source owners and trace the first missing permission edge. A
semantic repair is not yet justified. If the fixture hypothesis is confirmed,
add a separately named, correctly typed path through source annotation,
returned function, capture, fresh use and consumer while preserving all current
fixtures and assertions. The proposed Rust write lease is limited initially to
`candidate_effect.rs` tests and one source handoff. The parallel proof outcome
is a checked bridge from R104's inventory to the original Nat-route ownership,
including forest-head elision and choice-right tag 3, while keeping ViewLogic
separate from runtime `sourceOwners`.

The selector proposed a new primary-admitted contract, ≤2,400 seconds,
zero Astra, separate Rust and Lean lanes, fresh independent reviews before
integration, at most one justified Cargo invocation and one unique bounded
`/dev/shm` target with verified cleanup. No persistent build target or
environment is part of the proposal. This recommendation changes no R104
authority and is not itself a new lease.

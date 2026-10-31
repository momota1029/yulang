# R104 outcome

Status: `LEAN_GATE_PASS; RUST_PREEXEC_REVIEW_REJECTED; R104_V2_ADMITTED`.
Contract: `tasks/agent-loop/sprints/effect-permission-source-causality-20261101-r104.md`.
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
unreviewed for execution until the three findings are resolved and the fresh
review gate passes. All original R102/R103 failures and UNKNOWN/quarantined
leases remain intact.

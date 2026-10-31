# R75 admission receipt

Sprint: `EFFECT-PERMISSION-SOURCE-ROOT/20261031-R75`.

- Frozen contract: `tasks/agent-loop/sprints/effect-permission-source-root-20261031-r75.md`
- Contract SHA-256: `bbeb3cc4bf26a8fe29b2144dc086e6e0efa6bd7c0f9d2ec5ab8aeab8401db3fb`
- Frozen inputs: `tasks/agent-loop/sprints/effect-permission-source-root-20261031-r75-inputs-r1.json`
- Inputs SHA-256: `6bca174a95365afbf71a4919ec82f15b6ef7f5493880d9c6772a5d52bd116a9a`
- Baseline: `6cd31c3043f142a8500eb9ea8d8095a1296f4f8d`
- Authority: active continuing `research/simple-sub-intrusion`; no semantic or production scope change.

## Exact leases

| Worker | Exact write paths | Budget |
|---|---|---:|
| `/root/r75_rust` | `crates/yu-solver/src/candidate_receiver.rs`; `tasks/agent-loop/inbox/effect-permission-source-root-r75-rust.md` | 1200s |
| `/root/r75_proof` | `notes/theory/lean/YulangClosure/DistinctSourceEmissionRootR75.lean`; `tasks/agent-loop/inbox/effect-permission-source-root-r75-proof.md` | 2400s |
| `/root/r75_review` | `tasks/agent-loop/inbox/effect-permission-source-root-r75-review.md` | 1200s, only after author STOP receipts |
| `/root` primary | contract, manifest, admission, `tasks/agent-loop/current.json`, outcome/archive and Git integration | 1200s, at least 500s closeout |

The proof lane has one direct `--stdin` Lean audit authorized, bounded to 120s
and M1024, using the pinned already-installed Lean 4.35.0 executable. No Lake,
ordinary project build, Cargo, test, formatter, or emitted Lean artifact. A
second invocation needs a fresh written primary amendment before execution.
The exact checked input and output receipt must be frozen by the proof worker.

## Roster and resources

Live roster synchronized immediately before admission: `/root` was RUNNING on
this request; all other listed agents had completed their packets. No child was
RUNNING or WAITING, so no child notification or acknowledgement was pending.
Existing UNKNOWN rows, quarantined leases, 32 pending items, and the already
released R24 capacity reservation are preserved. No quarantined path is leased
or released. No environment, worktree, build output, cache, target, or scratch
path is created.

Admission grants only the bounded private evidence-construction repair and its
conditional typed-relation Lean theorem. Genuine R66 Root construction,
physical source/native extraction, original A/B, whole-language closure, and
production remain OPEN.

# R60 primary receipt — stopped on invalid Lake option

Sprint: `YULANG3-EXECUTION-PROOF-RECONCILIATION-20261026/r60`
Contract SHA-256: `427f73724eaf6e0c96bd55e33f419421cec606c10a3319bc907334a3b26c942b`
Baseline: `bfc2cb6455ddca5ba805276e1d9729a206d82dcd` on `yulang3`
Disposition: **STOPPED — PRIMARY COMMAND FAILURE**. This is an invocation/configuration failure, not a proof counterexample. No full build/audit result, review disposition, or new semantic acceptance is established.

## Frozen intake and pins

The distinct external source is commit `31b1473a9d90355903e1462a4f2f75abae75e48e`, with progress record SHA-256 `83f909b1e026604b8c3dd6b098869f6a1b66f1f50d58e1f853c45da3d2ea0c4c`. The R59 primary-capture failure and frozen candidate remain separate; R60 did not copy or import the R59 candidate.

A detached isolated worktree at the exact R60 baseline was created. All 23 frozen hashes in the R60 contract matched. The Lake binary resolved read-only to `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`, SHA-256 `8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1`.

## Durable native call receipts

The runner creates output files and persists a `STARTED` manifest before each process; stdout/stderr are written directly to those files. Runner SHA-256: `774627a90c1716b351d0c6887cb7aa90c1935818bb57788b38f9c83886e120c5`. Final manifest SHA-256: `1c54b7815cbee72f3b42023912578347ded2fedadae4fb487eb9cdc07bdc9459`.

1. `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --version` — exit 0, 0.474213084 s. Stdout: `Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)`; 53 bytes, SHA-256 `165f92ed239a8c7db772bf5ee9d58c59357b489951582a12c86dc9d8e06b23a2`. Stderr empty, SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
2. `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean --version` — exit 0, 0.123916241 s. Stdout: `Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`; 106 bytes, SHA-256 `eb22144228dd41cd51a0c84af4f976cd0cef473102dcf99b60be756b11f2b95a`. Stderr empty, SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
3. `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --no-cache build -j1` — exit 1, 0.071035524 s. Stdout empty. Stderr exactly `error: unknown short option '-j'\n`, 33 bytes, SHA-256 `6eb9f824393e2883798e31623b90151f66016b936934a979df7c696c1c0e0040`.

Cumulative recorded checker time is 0.669164849 seconds. Calls 1–2 verified the pinned version. Call 3 failed before starting a build because `-j1` is not a Lake option. Per the R60 contract, this first command failure stops the packet. Call 4 (complete audit) was NOT RUN. No corrected retry, extra checker, tests, Rust command, or reviewer call occurred. The process manifest records call 4 as READY; it must not be treated as an attempted audit.

All raw captures are preserved outside the repository at `/tmp/yulang-r60-execution-proof-reconciliation/call-01.stdout/.stderr` through `call-03.stdout/.stderr`, with the manifest and runner under the same directory. No Lean/Lake process remains. The isolated worktree has no tracked changes.

## Semantic boundary and next gate

Primary intake read the committed `BodyTyped` definition and the frozen R23 contract/adjudication/review. `BodyTyped` assumes a derivation under a shifted declaration table, empty graph, and explicit formal-value environment; its conditional use must not be treated as proving that every source-generated table has that schema. The authoritative source-embedding conclusion remains pending fresh review. R23, full executor/source correspondence, inference A/B, graph guardedness, source/native realization, and production remain OPEN.

The external commit and all its bytes remain untouched. R59 remains FAILED on its own primary capture gap. A fresh packet is required before correcting the Lake invocation or completing external-proof reconciliation. Questions remain withdrawn; no external proof was overwritten or merged with R59.

# INLINE-AUTHENTIC-EXTRACTION-20261027/r2 — stage 1 receipts

Status: primary-intaked provisional dependency/source-owner evidence. This is not
an independent review, extractor execution, Lean proof, or parent application.
Original full inference/executor goal and every parent gate remain OPEN.

## Admitted pins

- Contract: `tasks/agent-loop/sprints/inline-authentic-extraction-20261027-r2.md`,
  SHA-256 `af6c0f6e462f6ad414f7c82572216422925fe9ff3a68c1fe8d99df8f1605672e`.
- R2 parent source baseline: `232b024e0d793714027170a388ab746ce0d2b429`.
- Implementation assignment checkout: `1cc8406e3a70c29b04c0e48991b00cbf8812677b`.
  It differs because the admission contract commit followed the pinned source
  baseline. Subsequent `5065fb368eab3e0d7700d3f11b011d3e2be5c565` only records
  active assignments; source owners remain pinned by the hashes in r2.

## Implementation stage 1

Frozen handoff: `tasks/agent-loop/inbox/inline-authentic-extraction-20261027-r2-source.md`,
SHA-256 `4506d65a3e01d571c648c22150ee40294d2798056befdb93ea76c905290f2b31`.

Manifest `tools/inline-authentic-extraction/Cargo.toml`, SHA-256
`21c64b4a22318a1ae89c346357161812a6ac313b6f0c4999853272cf73e2832b`; isolated
workspace and only direct path dependencies are `yu-hir` with `shadow` and
`yu-syntax`. The `main.rs` contains only a minimal empty main needed for Cargo
target discovery; no extractor was implemented, built or run.

Lock `tools/inline-authentic-extraction/Cargo.lock`, SHA-256
`20ff9d78db7416d44659fc8e0145e28a5e8b8cfe3594bc34c5adf96f7e339214`.
Resolved graph `/tmp/yulang-inline-authentic-extraction-20261027-r2/impl/resolved-graph.json`,
SHA-256 `9c82bbe84e91d1cb567ae5dd998c9f8b2ac6c8fadebd65405c6918566aa4ac1e`;
metadata stderr/timing SHA-256
`aea5a9901b7f69afbe163b501aec48a2348f6a2611fc66b6dcee6457a98e4ce3`.
Graph: 26 packages/nodes, one workspace member, `yu-solver` absent from every
package/node/edge. The isolated lock matches 20/22 registry package tuples in
the root lock. The two exact mismatches are:

- `rowan`: isolated 0.15.19 / `a2441aaccb50f4267d4f0f58b21e0138e96a449f361ed57a2673a83c9bca0772`,
  root 0.15.17 / `d4f1e4a001f863f41ea8d0e6a0c34b356d5b733db50dadab3efef640bafb779b`.
- `unicode-ident`: isolated 1.0.27 / `a2c754d6c33795a1c324727428e5a7dedb5b06195f9890bdbcba760d3e246563`,
  root 1.0.24 / `e6e4313cd5fcd3dad5cafa179702e2b244f760991f45397d14d4ebf38247da75`.

Raw invocations, CPU 0 / 1 GiB / offline:

1. `cargo generate-lockfile --offline --manifest-path tools/inline-authentic-extraction/Cargo.toml`
   failed before compilation because the manifest had no target; exit 101,
   0.03 sec.
2. Same lock generation after adding empty `main.rs`; exit 0, 0.09 sec.
3. `cargo metadata --offline --locked --format-version 1 --manifest-path tools/inline-authentic-extraction/Cargo.toml`
   exit 0, 0.09 sec.

Three Cargo invocations are charged to r2. No compilation, extractor execution,
tests, Lean checks, installs or source/semantic changes occurred. The worker
stopped and requested a versioned primary decision before any additional write
or process. Total active time was not independently metered; these process
times are not a claim about total active work.

## Proof phase 1

Frozen handoff: `tasks/agent-loop/inbox/inline-authentic-extraction-20261027-r2.md`,
SHA-256 `afc9346b4653d111b30ad40a820a576a5e86aca7bc8dbc99722367e08b46298c`.
All 28 inherited pins were checked. Checker use: 0/6 calls, 0/360 seconds.

The inspected owners distinguish `SourceNodeKey` (parse, green node, start),
`HirParameterId` (source root plus ordinal), `LocalSourceIndex` (owner plus
arena ordinal), occurrence order (reassigned by source child traversal), and
runtime `Label(offset + ordinal)` / `SourceSite`. No equation was found in the
inspected cone mapping these into original `Site`, `Name`, `Declaration`, root
`Context` and ambient `ScopeEntry` telescope. Preserve the separate formal
coordinate and administrative `.wild` coordinate. This is a bounded owner
frontier, not a universal nonexistence theorem. The proof worker stopped pending
the executed trace and graph pin.

## Primary disposition / next gate

The dependency graph successfully avoids the unrelated `yu-solver` route, but
the exact-lock contract is not yet satisfied and the worktree/source-baseline
labels need a versioned clarification. The current lock and graph are frozen
inputs. Any lock alignment and metadata recheck require an explicit contract
revision; extractor code and compilation stay prohibited until Luna pins the
revised manifest/lock/graph hashes. The original proof/executor goal remains
active and OPEN.

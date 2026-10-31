# Sprint outcome — EFFECT-PERMISSION-MODULE-MATERIALIZATION/r2

Status: **CLOSED_INCOMPLETE / PREFLIGHT_TOOL_ERROR**. Contract SHA-256
`9dd7a7a6fc9059e5634cadef21923726ee82bcd4d66da5a8ce9ee82b7d1b8947`.
Neither supplier was semantically audited; no parent conclusion follows.

## Authentication disposition

Primary independently ran a complete 21-row SHA-256 manifest comparison with
Python 3 after validating the contract and every digest string. Contract and all
21 paths matched; `shadow_apply.rs` actual pin is
`c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`. This
primary receipt did not satisfy the contract's independent per-lane preflight.

Both fresh lanes attempted `python`, which was unavailable (exit 127) before
any interpreter started. Both stopped without a fallback. Their receipts
independently report that no manifest-listed source/design/handoff body was
read; each did read the r2 contract after the failed command in its orchestration
cell, and disclosed that sequence. No row is represented as authenticated by
either lane, and no supplier rule was inspected. This is an environment/tool
blocker, not a mathematical or semantic result. The R1 proof-lane sequencing
deviation remains recorded in its own outcome and is not repeated as an R2
source inspection.

## Frozen evidence and remaining work

| Artifact | SHA-256 |
|---|---|
| R2 contract | `9dd7a7a6fc9059e5634cadef21923726ee82bcd4d66da5a8ce9ee82b7d1b8947` |
| R2 source preflight receipt | `0756267a2a955d15de952207e7b3d22423660d05aea3574e580cbf3c59ca8257` |
| R2 proof preflight receipt | `dafb86a83cdc12b8b49bafab57a8fcb989cdad36ab8d7d5f2ad3e429c4225834` |
| R1 pin-mismatch outcome | `02023a50e96db1362ce5ded2eb1a4aa8f3b49a1a467186d5cd30e5ab586231e8` |
| Primary preflight | 21/21 manifest entries matched; no semantic source text printed by preflight |

No tests, build, Cargo, Lean/Lake, theorem, axiom audit, compiler/fixture/
expected-output change or Git operation. Both module Call suppliers remain
OPEN. Preserve original parent quantifiers/shared witnesses, the distinct
callback → Call result → tuple `left` obligation, all legacy UNKNOWN/quarantines,
and `DELTA_AUTH_UNRESOLVED / NO_SAFE_CODE_SLICE`.

The full 700-second r1 grant remains charged; r2's full 700-second reservation
also remains charged despite early stop. Cumulative charge: 1400 / 7200 seconds;
remaining ceiling: 5800 seconds. No time refund or reuse is claimed. Both fresh
r2 workers explicitly stopped and their receipts are frozen. Independent review
was not run because no semantic evidence was produced.

Next: selector consultation on the repeated preflight tooling blocker. Any
further contract needs a specified, available executable (`python3` or an
explicit non-Python alternative), a fail-closed preflight and new output paths.

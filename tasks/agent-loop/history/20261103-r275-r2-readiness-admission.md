# R275 revision 2 readiness admission — 2026-11-03

The prior R275 readiness STOP is authenticated at
`tasks/agent-loop/history/20261103-r275-readiness-stop.md`, SHA-256
`64fd4acbc229430549c30419bbf7004db4548737187976c6cec6d9a05899e9a1`.
Sol found 14 rendered excerpts missing one terminal LF. The full 300s r1
readiness charge remains. No coverage audit, fixture derivation, output write,
main trial or review occurred. The failed r1 contract/view and stop receipt
remain immutable.

## New exact packet pins

- Contract `tasks/agent-loop/sprints/source-acceptance-r275-r2.md`:
  SHA-256 `9c7c094bb9c10b1b25db8dc0db817c6c49da23c310170c67ea69f25a085bd80d`.
- View `tasks/agent-loop/sprints/source-acceptance-r275-r2-source-view.txt`:
  SHA-256 `a7e25ef8172692ca1d3b332245d96ba736fa906a8318bb225ed0e17713683655`.
- Index `tasks/agent-loop/sprints/source-acceptance-r275-r2-view-index.json`:
  SHA-256 `cf9faefef5471c669039e74f2181beebc41226898e89acdb4c7789d20653eb79`.
- Reused unchanged ranges: SHA-256
  `1cdc644abb143a068cbea0113bca1a9b9ca673e7c92eff1cc81f09b863c6c114`.
- Reused unchanged coverage: SHA-256
  `9081065d51532ac50cb31d1d1befdc5fd601bbecd6b5257eba4148806968c598`.
- Authenticated 229-path inventory: SHA-256
  `42040552635bb7c2652eb0bad68cb46295078d03ae70620b7edd555d3883fa5f`.

Luna's pre-contact gate independently rechecked all 35 exact indexed payloads
against the original inclusive byte intervals, whole-file hashes and excerpt
hashes; verified unique IDs, in-bounds offsets, non-overlap, and exact
35-ID correspondence with the ranges file. Indexed payload bytes preserve
terminal newlines. No technical trial or source-body reasoning occurred.

## Proposed gated resources

Same named Sol trial identity `/root/sol_r274_source_acceptance`; all prior
charges retained. Before any R2 readiness work: contract-only acknowledgement,
identity/session check, live-roster synchronization and Luna's explicit
readiness GO. New readiness cap: **300s**, restricted to contract/view/index,
unchanged ranges/coverage/inventory/manifests and hash-only original-file
checks. The r1 attempt's missing boundary and caller/callee audit remain part
of this gate. No fixture derivation or producer outputs in readiness.

The r1 unissued main/reviewer reservations remain canceled. R2 separately
allocates a 1,500s main trial after full readiness adjudication, a fresh 1,800s
review only after coherent producer freeze and exact output pins, and 150s
additional Luna correction/adjudication. Original Luna 600s allocation is
retained. Accounting ceiling is **4,650s**: r1 readiness 300 charged; original
Luna 600 retained; r2 readiness 300 newly reserved; main 1,500 gated; review
1,800 unissued/gated; extra Luna 150 newly reserved. No refund/reset/extension.

Producer output paths remain absent and their existing exact leases remain
held for `/root/sol_r274_source_acceptance`:

- `notes/theory/2026-11-03-source-acceptance-r275.md`
- `tasks/agent-loop/inbox/source-acceptance-r275.md`

Recheck absence and ownership before main GO. No production edit authority;
parent/A/B 0→0, Need_D/R71 OPEN and `NO_SAFE_CODE_SLICE` unchanged.

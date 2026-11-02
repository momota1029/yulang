# R275 revision 3 readiness admission — 2026-11-03

The r1 LF serialization stop and r2 constructor-coverage stop are preserved at
their pinned receipts. Both Sol readiness stages consumed and charged 300s.
R2's byte integrity gates passed, but its coverage table missed the mandatory
`parse_root_statements` wrapper, misattributed HIR owners, omitted the full
candidate collection continuation, and failed to close a positive production
entry/flag route. No fixture derivation or output writes occurred.

## R3 packet and pre-contact gates

- Contract `tasks/agent-loop/sprints/source-acceptance-r275-r3.md`:
  SHA-256 `4e30e9c048596a57da7cfa80fe1261e67e2db17f2ba8c07e70dc3961b02138c5`.
- Ranges: SHA-256
  `2cd3ad9dc9a66129a42ec11d8d45ef4b78a0a877d0d066dc262313d524c03c3e`.
- Binary view: SHA-256
  `6b3836953c876c40f2cda0b944ff5f8a8d912d179e5ac58f9e93c7e6d38e8373`.
- Byte-offset index: SHA-256
  `0966c2429bb64896bd31de52f2e20609642c2a75bba6dae3cf5fec46ebcb94e5`.
- Corrected coverage table: SHA-256
  `61d22ccc8004305fb377a12556cd53550926c59cb5857a55b0f01f5921e775cb`.
- Entry/flag owner index: SHA-256
  `74ec95494935e803296f8ab276b6237369253f73d3df57ec2bc5f33f12426481`.
- Authenticated inventory: SHA-256
  `42040552635bb7c2652eb0bad68cb46295078d03ae70620b7edd555d3883fa5f`.

Luna pre-contact validation passed for 229 authorized path entries and 41
exact byte payloads, with whole-file/excerpt hashes, exact view equality,
unique authorized IDs, bounded nonoverlapping index slices and production
interval test-boundary checks. The original two producer outputs remain absent.

## Narrow R3 readiness stage

After a contract-only WAITING acknowledgement and live-roster/session check,
reuse stopped Sol identity `/root/sol_r274_source_acceptance` for **300 seconds
of readiness only**. All earlier Sol charges remain intact: R272 2,400s,
R273 3,000s, R274 2,400s, R275-r1 300s, R275-r2 300s; **8,400 seconds before
R3**. No reset or refund.

Readiness verifies every R3/inherited pin, 229 input hashes, the three
origin-manifest hashes, all 41 original-file and interval hashes, exact indexed
payload bytes, the production/test boundary, the corrected constructor table
and the entry/flag provenance index. In particular, it must exhibit a positive
authenticated production path through the required candidate flags to source
emission and static-SCC collection. The visible ordinary collector forwards
`candidate_values=false`; test-only call locators are not evidence. A
text-search absence is not a production-unreachability theorem. If readiness
cannot establish a positive production route from the bounded source owners,
STOP and report the exact entry/configuration seam; no main-trial GO.

No fixture derivation, producer writes, tests/builds/probes, raw source-body
display, code changes, reviewer, Astra or descendants are authorized in this
stage. Sol reads source bodies only from the R3 indexed view; original files
are hash-only.

## Accounting and later gates

The fixed R275 retained/allocated ceiling is **4,650 seconds**:

- r1 readiness 300s charged;
- r2 readiness 300s charged;
- r3 readiness 300s newly gated;
- main trial 1,200s newly reserved after complete readiness PASS;
- fresh independent compiler referee 1,800s unissued until coherent freeze;
- Luna 750s retained/allocated (600s original plus 150s revision).

The prior 1,500-second r2 main reservation was canceled; r3 re-reserves 1,200s
by moving 300s to the required entry-provenance readiness. The previous
reviewer reservation remains canceled and is reissued only after coherent
producer completion and exact frozen output pins. No automatic extension.

The unchanged output pair is
`notes/theory/2026-11-03-source-acceptance-r275.md` and
`tasks/agent-loop/inbox/source-acceptance-r275.md`; both are absent and remain
held for the same Sol identity. Recheck absence and ownership before any main
GO. Parent/A/B remains 0→0, Need_D/R71 OPEN, and `NO_SAFE_CODE_SLICE` remains.

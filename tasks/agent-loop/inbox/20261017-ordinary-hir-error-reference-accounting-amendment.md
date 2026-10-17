# Frozen amendment handoff: ordinary HIR error-reference accounting

Assignment ID `ordinary-hir-error-reference-accounting-amendment`, revision 1.
Primary author `/root`, primary Luna; no descendants. Sprint
`ordinary-hir-application-admission-implementation-20261017`, revision 2 frozen, based on `b1f15a81a` and current counterexample checkpoint
`8be4b8248`.

## Inputs and outcome

- Adopted design rev4 SHA-256:
  `2e61e2acb1a8981bb78592accc48207a24a5cc4c75278e100f63eb960acfeea3`.
- Astra proof/counterexample SHA-256:
  `226d389d8fb68b6ddec328dd0f6ece4a4f3f2e344eff3f434d10b0a3d02b37ad`.
- Astra handoff rev1 SHA-256:
  `28cc30876831203661ea237c20925249ac48ed5a9cc7fa648c36491dcb51d062`.
- Amendment SHA-256 `e8b53a773675ba54f0cb5dcc4d62a993e8dd16954e0c92c58fdfc80c620d411e`.

Astra's exact family has `V=2m+1` nodes, `E=m+1` error records and
`R=m(m+3)/2` physically stored descendant-error references. The aggregate
linear-storage claim in rev4 §2 is false for the unchanged §4 flat
`Box<[HirErrorId]>` subtree lists. This is a resource counterexample only; it
narrows no source grammar and refutes no original theorem.

The amendment proposes `O(V+E+R)` construction/storage for nodes, error events
and all specified flat references, excluding spelling bytes, source-map lookup
costs and unchanged module/carrier passes. Each aggregate reference must be
written once; child subtree disjointness and unique leaf error events supply the
no-duplicates argument. Worst case is `O(V^2)`. Counts/reservations use checked
arithmetic and include all R references before any publication. Actual code
strategy/fixture measurements remain open. API/diagnostics/ID behavior is
unchanged. Proposal is not adopted pending sequential compiler -> spec ->
architect reviews and Luna adjudication.

## Review questions and scope

1. Verify the grammar member and exact lower-bound count; distinguish error
   records from repeated references.
2. Check the proposed output-sensitive bound against rev4 §2/§4 and the pinned
   `Box<[HirErrorId]>` representation; require an explicit construction argument,
   not only defining R.
3. Check checked aggregate arithmetic, fallible reservation and module/stage
   atomicity; no source restriction or observable error/API changes.
4. Keep original Call/A-B/F1/FK1/source/native/soundness/principality/termination
   gates OPEN.

STOP/authority: no code, tests, Cargo, builds or probes are authorized under
this amendment lease. Only the primary may adjudicate after all independent
reviews freeze their receipts. Preserve all UNKNOWN leases.


Primary resource receipt: Astra's frozen file reports a 420-second charge at its
09:27:05 freeze checkpoint; its later STOP message reports final elapsed wall
429s through 09:27:54. Luna charges 450/720s conservatively from the final STOP
message and retires the remaining270s; the earlier frozen checkpoint estimate
is retained as a checkpoint, not silently rewritten. Luna's amendment-author
reservation is charged90/90s.

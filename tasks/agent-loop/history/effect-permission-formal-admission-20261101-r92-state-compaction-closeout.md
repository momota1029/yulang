# R92 closeout state compaction before R93

Before R93 admission, `tasks/agent-loop/current.json` was the blob
`d97380cd5bda68b091c113c10f216fc10af5e54e` at commit
`21777269598c0629d31e1b6684c87b0c1eebe724` (16,256 bytes). It records R92 as
`CLOSED_BOUNDED_EXECUTION_BLOCKED`, with one of two calls used. The exact call
failure and bounded source finding remain in the R92 proof/source/review
handoffs and closeout commit. Its unused second-call slot is closed, not rolled
into R93.

For R93 admission, compact state removes only the confirmed STOPPED rows
`/root/r92_formal_admission_proof` and `/root/r92_flattened_input_review`, plus
the resolved R92 sprint contract, input manifest, admission, closeout
compaction, and frozen proof/source handoff leases. These files and bytes stay
in Git and remain referenced under `previous_sprint`. No UNKNOWN worker,
quarantined path, unresolved pending item, or unrelated lease is removed or
changed. The existing authenticated 13-slot capacity release is unchanged; no
new capacity override and no path release occurred.

The new R93 exact leases are limited to its new proof module, proof handoff, and
source handoff. R93 review output is leased only when the independent reviewer
is assigned. The current state retains all 32 pending items and stays below the
16 KiB limit.

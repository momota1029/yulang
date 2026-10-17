# Implementation handoff: receive-applied Replay observation

Contract rev1 `3223aec16eb3026a874676492c334199433b3333f539375e8ad3064107e4b23d`,
baseline `aa808f96543474d85fe70fba92161f94cf4cfd9a`. All twelve direct source
pins matched before edits.

Frozen companion fixture differs from the unchanged original only by the
trailing `my received = receive f0`. The harness uses the companion file for
`include_str!`, disk-byte comparison, and exact `ModuleIdentity`. It requires
one `received` LocalSource Apply whose operands resolve to the exact
`ModuleDef(receive)` and `ModuleDef(f0)`, with the candidate observer matching
the same source Apply and its owner/operand/key/scope evidence.

No tests/build/runtime command ran after this freeze. Await fresh CLEAN compiler
review and capacity remeasurement (at least 120 seconds) before the single
authorized observer run, capped at 120 seconds. Prior local-route focused
attempts are summarized in the progress note and do not count as this companion's
runtime evidence. Replay reachability remains unobserved. The source/native
proof handoff is frozen at
`notes/theory/2026-10-18-receive-applied-source-correspondence.md`
(`e636422256e63af9cb04b8962f95fd0fbc845283aabcc7635c07fe5483d4e503`) and
`tasks/agent-loop/inbox/20261018-receive-applied-source-correspondence.md`
(`5401a12dccbbe997734bc6887c30e0d8b22f74de83271bd256d491a438dbfac9`). Its
static source snapshot records companion SHA `7d7ad10d00773ecef583c53a1d546737dbf92daf75a9637f45c03798eb893fad` and harness SHA `eb7e5aae0f29d9277ba191dc965918a6110eca8f054417aa44bbb0cec1f414e6`.

## Luna integration addendum rev2

The sole authorized command ran once after CLEAN review and capacity
remeasurement; exact command is in the progress note. It exited `0` and reached
candidate inference; available output confirms `received` operands resolve to
the companion's exact `ModuleDef(receive)` and `ModuleDef(f0)`, with
`candidate.source_call[3]` matching the Apply source. The tool truncated the
captured stdout inside the Replay/relation rows, and no complete transcript is
available. Therefore demand-bearing Replay status is **UNKNOWN**; the command
was not retried. Original theorem closure stays0/OPEN. The prior inbox revision
is preserved as the committed `ad4af2393` snapshot; CLEAN review covers that
snapshot, not this post-run documentation addendum. Previous inbox SHA:
`b7237dd9653ff3c241c01868906ccef3cd86b43b4d02ded35485fa437425e822`.

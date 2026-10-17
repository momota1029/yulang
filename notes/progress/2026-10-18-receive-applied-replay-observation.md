# Receive-applied Replay observation

## Frozen source setup

Sprint `npair-applied-fixture-replay-observation-20261018`, contract rev1 SHA-256
`3223aec16eb3026a874676492c334199433b3333f539375e8ad3064107e4b23d`; baseline
`aa808f96543474d85fe70fba92161f94cf4cfd9a`. All twelve direct input pins in
the contract were rehashed and matched before edits.

The companion `tasks/agent-loop/fixtures/20261018-receive-choose-applied.yu`
copies the pinned receive/choose fixture byte-for-byte and adds only the final
declaration `my received = receive f0`. The original fixture is unchanged. The
research example reads the companion path both from `include_str!` and disk,
uses that exact path in `ModuleIdentity`, and requires exactly one `Apply` in
the HIR-owned `received` source. It checks that the callee is
`ModuleDef(receive)` and the argument is `ModuleDef(f0)`, then checks the
candidate `source_call` against the same Apply occurrence, operands, keys,
owner, and scopes.

The companion, harness, and this handoff are frozen for independent compiler
review. The source/native proof handoff is frozen on its separate lease:
`notes/theory/2026-10-18-receive-applied-source-correspondence.md` SHA-256
`e636422256e63af9cb04b8962f95fd0fbc845283aabcc7635c07fe5483d4e503` and
`tasks/agent-loop/inbox/20261018-receive-applied-source-correspondence.md`
SHA-256 `5401a12dccbbe997734bc6887c30e0d8b22f74de83271bd256d491a438dbfac9`.
That proof's final source snapshot records the same companion and harness hashes
and requires the exact `ModuleDef(receive)` and `ModuleDef(f0)` operands.
No test, build, or runtime command has run on this snapshot. The planned
observer command is authorized only after fresh CLEAN review and a fresh
capacity measurement of at least 120 seconds; one command maximum, capped at
120 seconds. Runtime status: not run; Replay reachability not established.

## Previous-runtime evidence carried forward

The prior local-route focused command first exited 101 before tests due to
`FrozenInferenceData` lacking `candidate_source`; no tests ran in that attempt.
After the scoped selector fix, the focused retry compiled, passed two existing
tests, and failed three new tests at lines 328, 350, and 374; the receive/choose
fixture was not run. Those regressions were updated to use
`lower_module_with_local_source`. This previous evidence is not a runtime result
for the new companion fixture.

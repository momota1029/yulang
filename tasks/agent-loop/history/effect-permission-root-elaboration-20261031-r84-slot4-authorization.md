# R84 Lean slot 4 authorization — final repaired Root candidate

Primary authorization for invocation 4 of the four-slot ceiling. Slot 1 (normalized prefix) exited 0; slot 2 remains unused; slot 3 (full candidate) exited 1 and was independently reviewed. Fresh source review of revision 2 returned PASS. This authorizes exactly one final candidate invocation and accepts no theorem before its own complete output is audited. No fifth invocation is permitted.

## Frozen evidence

- Contract: `tasks/agent-loop/sprints/effect-permission-root-elaboration-20261031-r84.md`, SHA-256 `28890c4ee0953c4a4e01a1f5a95b04b22eaa45616d87a4f3b5a9ad2a8d6604f0`.
- Pre-authorization input manifest: `tasks/agent-loop/sprints/effect-permission-root-elaboration-20261031-r84-inputs.json`, SHA-256 `8917c32d75cd403fb40f63699965cc494ecc14f73130fd4c4fadbecaf10f7eb7`.
- Candidate r2: `notes/theory/lean/YulangClosure/ConstructedPhysicalRootR84.lean`, 22,427 bytes, SHA-256 `5d8ad6429906cdf971dbb9ee44841223c1fcc28e6591e1a75d1f453ea4eac13d`.
- Proof handoff r2: `tasks/agent-loop/inbox/effect-permission-root-elaboration-r84-proof.md`, 339,182 bytes, SHA-256 `8241f3b7ab3a656c15d114a987159fd33c66f04ae48fc3d82dbda0e4972ed17b`.
- Independent review receipt: `tasks/agent-loop/inbox/effect-permission-root-elaboration-r84-review.md`, SHA-256 `923f32c698d92d5e06d50258d73a5a3a2150884b1c86815bf129988e5e900214`; PASS for r2 source and exact slot-4 input. Reviewer did not run Lean.
- Slot-3 failure receipt: `tasks/agent-loop/history/effect-permission-root-elaboration-20261031-r84-slot3-raw-result.json`, SHA-256 `db6ceb58d4fa88755d1b2136cef45ae46af0374e1a870919df361ba8b9ee7d91`.

## Exact authorized invocation

- Recipe: the accepted normalized prefix body (78,934 bytes, SHA-256 `ee4abd52c66c46bf714ca196be6de1fbb46ee2f2f31e17dd882a9c367b14ab49`) + import-stripped r2 candidate + one newline + the unchanged `full_queries` from the proof handoff.
- Exact stdin: 103,470 bytes, SHA-256 `93b365ddf908e223558d166efe7f76a1f5c370a5b1c9080716d0fb0ce92b3df0`. Primary independently reconstructed this exact byte string from all pinned source slices, six normalization receipts, candidate, and thirteen queries; it matches the reviewer and handoff.
- Executable: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, SHA-256 `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
- Command: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin`.
- Working directory: `notes/theory/lean`; environment `LEAN_NUM_THREADS=1`; hard timeout 120 seconds.
- Reconstruct and hash-check stdin in memory, supply it directly to Lean, capture full stdout/stderr in memory, then persist exact streams and resource/exit metadata to the primary result artifact. Do not print streams or base64 into tool output.
- No Lake, build, tests, formatter, cache, `.olean`, target, scratch, environment, or worktree creation.

The reviewed source repair maps all ten slot-3 diagnostic targets to explicit changes and preserves all thirteen original claims. Slot 4 is the sole remaining invocation. Acceptance requires process exit 0, all thirteen complete theorem types and transitive axiom reports, no error recovery, `sorryAx`, project axioms, `Classical.choice`, or native-evaluation shortcut. Any failure closes R84 incomplete.

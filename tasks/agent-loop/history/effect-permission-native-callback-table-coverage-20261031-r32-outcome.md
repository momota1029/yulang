# R32 outcome — CLOSED_PASS / COVERED_FINITE_PROJECTION

R32 repairs R31's faithful-projection coverage gap for the covered finite-projection artifact gate. Rust source-owner mapping, checked Lean construction, and independent review all passed their stated gates. This closeout does not establish native extraction, original A/B closure, or production.

## Frozen and reviewed evidence

- Rust source-owner mapping: `tasks/agent-loop/inbox/effect-permission-native-callback-table-coverage-r32-rust.md`, SHA-256 `288c5b448e4fd7e2531e52d6689037700cfd7c1aca6ae07c653c3129cbd1dcb7`. It traces typed request, consumer, selected Catch operation, and complete closed permission-family row into one candidate HIR snapshot. Selected arm Debug serialization is explicitly lossy and not used as identity evidence. No source modification, compile, or runtime result is claimed.
- Lean module: `notes/theory/lean/YulangClosure/NativeCallbackGrantBridgeR32.lean`, SHA-256 `bf2908ae347814c71ddc32ffae0f64a62103b855d96655a47aa1b9db0dc9690c`.
- Proof/audit handoff: `tasks/agent-loop/inbox/effect-permission-native-callback-grant-r32-proof.md`, SHA-256 `be7b68b1682f709bad5c624ca57e27a806df63848f7eafe938710ca84438a0a0`.
- Independent review intake: `tasks/agent-loop/inbox/effect-permission-native-callback-grant-r32-review.md`, SHA-256 `114d5456a3ab902835b3fa2f781ad49b84a359e857b540dd2c44d21beb4e0547`. Reviewer returned PASS with no blocking, major, or minor correctness findings; the intake is Luna-authored because reviewer remained read-only.
- R32 contract SHA-256 `85f1bd3d6350be8c501b0859230389d288901cceb9aa4982e57784842dcb5817`; input manifest SHA-256 `91495c9955c39ce6988421d1913803788c26aca3d8d8ea47c224d837dcb0ef66`.

Pinned Lean 4.35.0 stdin audit under read-only `bwrap` exited 0 with all 41 theorem types and full axiom reports, empty stderr and no diagnostics. Lean construction/repair/audit/handoff interval was measured at 254.332 seconds; startup was unmeasured. Rust aggregate, reviewer aggregate, and primary aggregate time are UNKNOWN. The review independently ran three successful pinned stdin audits (7.198409932 seconds total); its aggregate review time remains UNKNOWN. No residual resource allocation transfers to a successor.

The covered table is constructed from request/consumer/arm IDs and the full permission row. Round-trip decoding, full-row membership equivalence, and the empty-table falsifier are connected to `covered_checked_catch`; the theorem returns all three operation decoder witnesses and the family equivalence. New theorem axioms are only `propext` and `Quot.sound`, with three new declarations using no axioms. Exact R31/R26 module prefixes remain intact. The reviewer confirmed all 41 declarations and axioms and the source-owner mapping against the pinned archive.

## Remaining open obligations

R32 provides mathematical local coverage and archive source-owner evidence; it does not translate the serialized HIR-relative coordinates into Lean's local table indices. Native extraction must still bind coordinates to one authenticated HIR snapshot, recover faithful identity atoms, validate numeric conversion/ranges, authenticate annotation/Name/Apply provenance and the complete source row, establish request-owned observation and actual Grant/invocation guard provenance, extract dynamic Catch/arm data, and show actual request emission and native `Step`/`History`. `entryWithRow` projects a supplied row and `callbackSlice` constructs supplied-record state; neither authenticates native execution.

Original all-source A/B, whole-language effect hygiene/soundness, principality, progress, termination, and production remain OPEN. Frozen authority and source claims are unchanged.

## State and Git

All R32 producers and reviewer are STOPPED with no descendants. The seven absent R29 path leases listed in the stage ledger were retired; existing R29 handoff records remain. Unrelated UNKNOWN writer quarantines remain unchanged. `python3 tools/agent_sprint.py check` passed after synchronization.

No R32 commit or push was produced. The workspace's `.git` path is read-only in this execution environment and previous Git mutations were rejected; no retry was made. R32 scheduling records are archived in its contract, admission, stage ledger, review intake, and this outcome. A successor must use a fresh envelope and pin these frozen outputs; it receives no R32 time.

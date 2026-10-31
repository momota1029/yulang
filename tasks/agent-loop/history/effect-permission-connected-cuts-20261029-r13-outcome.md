# R13 outcome — `CLOSED_COMPLETE_CONDITIONAL`

Sprint: `EFFECT-PERMISSION-CONNECTED-CUTS/20261029-r13`  
Contract SHA-256: `3b723f1a4153af9217717bedcdb5ff1c06da569014219b00feef976057723a19`  
Input manifest SHA-256: `911ea88407dc079f56ee19914a2ab3be49654cc2182ee6a2adb0302cc5d8c880`  
Pre-close current-state archive: `tasks/agent-loop/history/effect-permission-connected-cuts-20261029-r13-state-archive.json`  
Archive SHA-256: `9736f4ecebac757f6006f3069007583b0127fbb709d766379749f5ab3c522353`

## Accepted result

- Proof artifact: `notes/theory/lean/YulangClosure/FormalPermissionConnectedCuts.lean`, rev2 SHA-256 `6427eed5f0c3b84f80a3a37c31797fc782960c725fb77f6bef46cebcc993b023`.
- Proof handoff: `tasks/agent-loop/inbox/effect-permission-connected-cuts-r13-proof.md`, SHA-256 `c677e958bb6ef11af36f3a77e1b4f95c6980b9d762eba27a4bf1e1a504d31fb0`.
- Source handoff: `tasks/agent-loop/inbox/effect-permission-connected-cuts-r13-source.md`, SHA-256 `99614e24f70946b929bf6ec539244d58e111739e0dbc20ec9e7651fef7d144d7`.
- Independent review: `tasks/agent-loop/inbox/effect-permission-connected-cuts-r13-review.md`, PASS with zero blocking, major or minor findings; SHA-256 `fb1f43e3c486237b9f93d6955f4bf4cf96b5b3827a40c42044838e099734c394`.
- Primary Audit 2: pinned Lean 4.35.0, exit 0, 16.33s, 977212 KiB peak RSS; all 19 inherited/new theorem roots emitted complete types and transitive axiom reports. Audit 1 parser/build failure is preserved and is not a mathematical counterexample. Audit plans, 16-file copy receipts, tool hashes, raw stdout/stderr/status/resource receipts are in `/tmp/yulang-effect-permission-connected-cuts-20261029-r13/`.
- All 145 admitted input entries and both 16-file isolated project copies rechecked with zero missing/mismatched files. Static `python3 tools/agent_sprint.py check` passed.

R13 constructs all 13 cuts from one connected HelperState trace, proves structural full/relative path round trips and preserves Metadata/allocation identity and sibling distinction, threads four allocator pushes and two ordered permission appends, and applies R12/R11/R9 to the same output witness.

## Scope still open

This is a conditional operation-model construction. It does not establish actual Rust helper execution correspondence to the modeled Calls, reservation availability or machine arithmetic, primitive/alias authenticity, native identity/publication, the original parent, consumer residual/effect hygiene, soundness, principality, progress, termination or production.

## Next selector proposal

`/root/r21_closeout_selector` recommends `EFFECT-PERMISSION-TERM-CALL-CONTROL/20261029-r14`: construct the successful `with_term_events` call transcript from its constructor result, capacity-event sequence, accounting flag and sampler outcomes; preserve return/error order and apply to R13's term-call cuts. This is proposed only; exact leases and admission are Luna-owned.

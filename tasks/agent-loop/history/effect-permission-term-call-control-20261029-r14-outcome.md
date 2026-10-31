# R14 outcome — `CLOSED_INCOMPLETE`

Sprint: `EFFECT-PERMISSION-TERM-CALL-CONTROL/20261029-r14`  
Contract SHA-256: `8a1fec9211b0962f3f2233f0dc35d097eadfe5c42267df51a7f0ad0b9e1e1a90`  
Input manifest SHA-256: `ec157c6b0a0fca8416873b2bd8c3e44f8bd679a4015f19279368a3d12aa0e584`  
Pre-close state archive SHA-256: `2a363b4e16480e72b9e13b749fe0685af6e44710d31c58afeced1f2918291f16`  
Artifact archive: `tasks/agent-loop/history/artifacts/FormalPermissionTermCallControl-r14.lean` (SHA-256 `fde5e86c3540646b778856dda985b51db201a20ab7a38ca3e34485257c2dbfdc`)

## Preserved candidate and diagnostics

- Candidate artifact `notes/theory/lean/YulangClosure/FormalPermissionTermCallControl.lean`: `fde5e86c3540646b778856dda985b51db201a20ab7a38ca3e34485257c2dbfdc`.
- Proof handoff `tasks/agent-loop/inbox/effect-permission-term-call-control-r14-proof.md`: `0ac4030c1fdbcfe9947876cdc8eee2d5403adfca00d95588759552e83a080c77`.
- Source handoff `tasks/agent-loop/inbox/effect-permission-term-call-control-r14-source.md`: `744c3244b919758360c3e0f966278ebbc3881d2cd1120de19410e345340c65ce`.
- Audit plan correction: original plan `33d3aa8297e784180b6ad06030fab59ac3bd8ae5c1747dc74c1f70e584e2c3bb`; corrected plan `11dae13aba5d3a486df5763984bee71fd6171cd50f495387e8612e83818bace6`.
- Preflight path error launched no checker/Lean/Lake: receipt `bfc1d61c17259c6a149e8193c61a66c51d6ee1fff1edb3eecb9c6a869b592ded`.
- Actual primary Lean 4.35.0 Audit 1 build failed, exit 1, 14.67s, peak RSS 798108 KiB. It emitted zero theorem types and zero axiom audits. The only proof error is an unsolved true-branch goal in `control_test_fields` at line 231; this is a proof construction failure, not a mathematical counterexample.
- The fixed 600s proof writer stopped at cap. The second audit slot expired unused; no reviewer was started. No proof/production gate is accepted.

All raw outputs/resource receipts and the 17-file isolated project copy are preserved under `/tmp/yulang-effect-permission-term-call-control-20261029-r14/`. The 153-entry manifest had zero missing/mismatched inputs. Static `python3 tools/agent_sprint.py check` passed after failure-state synchronization.

## Next selector proposal

`/root/r21_closeout_selector` recommends `EFFECT-PERMISSION-TERM-CALL-CONTROL/20261029-r15`: proof-only repair of `control_test_fields` with unchanged statement/model, full 38-root audit, then fresh independent review. Proposed envelope 800s: lean_prover 300s, primary read-only source 100s, fresh reviewer 250s, primary 150s; no Astra/descendants. Actual Rust constructor/sampler linkage, primitive/alias authenticity, reservations, native publication, original parent, effect hygiene and production remain OPEN.

# Source-evidence handoff: observed Apply ingress

Evidence note: `notes/progress/2026-10-18-npair-observed-apply-source-evidence.md`, SHA-256 `9ac03afa281bea0236f87f01dae086fc618e4a2ee6932ea631d55d9c7125b851`.

Contract: rev2 `tasks/agent-loop/sprints/npair-observed-apply-function-ingress-20261018-rev2.md`, SHA-256 `6792708386e9d977d8905716a2f79cc831fd5e37ad8f5e1d1b683919ddf8d0c8`; baseline `5c45c1807fc6f4fa495a2f0b85c4bdba1672820d`.

## Result

The one permitted harness command exited 0. It directly observed `received` HIR binding -> LocalSource -> Apply occurrence 18 -> candidate `source_call` occurrence 18. The outer operands were `receive` (occurrence 19, `ModuleDef(receive)`) and `f0` (occurrence 20, `ModuleDef(f0)`); the candidate printed native call endpoints and had no conflicts. HIR also printed `UnsupportedExpression` for the expression, so this is direct positive LocalSource/collection evidence despite that diagnostic, not a claim that HIR accepted the binding normally.

At run time, the query selected the printed call through owner-root and Apply-occurrence membership and printed operands/native terms. Later, unexecuted edits added exact source-key, child-index, and scope comparisons, a four-child Function print, and aggregate scoped dependency/relation-flow dumps. Current example SHA-256: `5525939261a25548f5694c06cef330dcf4e53079b6d5377b0a3cd87d4e2b8d12`. No second run is permitted in this packet; those later query checks are not runtime evidence.

## Open correspondence

Strict typed endpoint/scope equality, a Replay tied to this call, the ordered lower/upper BoundKeys and their relation fibers, and the original parent theorem remain unobserved/open. Aggregate Debug dependency and flow output cannot by itself bind an edge to these exact call handles. Do not infer `s1 -> D`, same `R1`, or full parent closure from this run.

Fixture restored to baseline SHA-256 `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`; the only temporary edit was `my received = receive f0`. No other fixture changes remain.

## Resource and stop

Requested: Luna / implementer / high, 720s cap. Observed model/effort, task-clock start, and total active elapsed/remaining time: UNKNOWN. The exact one command is consumed; exit 0; Cargo reported build time 1.60s. No other checks/builds ran and no process remains active. Known scratch paths: none. Status: STOP; review or continuation requires primary disposition and any new explicit contract.

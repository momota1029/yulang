# N-pair observed Apply ingress sprint closeout

Sprint `npair-observed-apply-function-ingress-20261018`, rev2 contract SHA-256
`6792708386e9d977d8905716a2f79cc831fd5e37ad8f5e1d1b683919ddf8d0c8`.

## Outcome

1. Original parent conditions genuinely closed: **0**. The reviewed constructor
   proof establishes actual Apply demand construction, all four Function
   children, same-R1 installation/fresh-use, and the successful-path native
   port equation `q_D^r = phi_r(rep(q_D))`. Same-original-w contribution
   `eta`, dependent Permission/use `T_rho`, actual runtime Replay records,
   N-Transport and the parent remain open.
2. The single source run reported LocalSource/Apply occurrence 18, matching
   source_call occurrence and native endpoints. The strict endpoint/scope and
   ordered-Replay query edits were added after that run and remain unexecuted;
   they have been reverted. Fixture bytes match the baseline. The observations
   remain provisional and author-reported, as detailed in
   `2026-10-18-npair-observed-apply-run-provenance-correction.md`.
3. Next critical-path item: derive the authentic same-w contribution incidence
   `eta` at returned Written `s1`, preserving provider, reference, theta, world,
   assignment, scopes and lineage. Runtime `s1 -> D` / Replay evidence cannot
   replace `eta`; only after this source premise is constructed should the
   dependent `T_rho` transport be attempted.

## Review, deviation and integration

The constructor-law proof received a fresh independent CLEAN review within its
stated scope. The implementation review found a MAJOR process deviation: rev2
required the frozen strict query and independent review before the one Cargo
run, but the run preceded that gate and no executed harness snapshot was
captured. The primary retains the output only as a provisional
author-reported lead. The independent delta review of the provenance
correction was CLEAN; it does not retroactively satisfy the run gate. The
remaining source-example diff was explicitly reverted, so no unexecuted query
is represented as verified implementation. No second run was made because
packet elapsed and remaining time are UNKNOWN.

## Checks and Git

`python3 tools/agent_sprint.py check` passed as a static state check. It does
not verify the proof, execute the compiler or independently authenticate the
run. The exact fixture baseline hash is
`969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`; the
research example was restored to repository HEAD hash
`10ea5f2c6db7c9d093d86780dbeb217d7eca11332e99a4d1ec40f4753f544e7c`.

The frozen proof, source-evidence note, source handoff and provenance
correction are integrated as separate receipts. No semantic rule, theorem
quantifier, accepted source domain, fixture expectation or production compiler
path changed.

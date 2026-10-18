# R57 Luna source-owner handoff

Assignment-ID: `R57-ORIGINAL-NAME-TWO-CAPTURE-OWNER-TRACE`.
Author/worker: `/root` (Luna primary; read-only source-owner lane).
Sprint: `original-name-two-capture-20261019-r57`, revision 1.
Contract SHA-256: `b8fb35aa130304ab459b1c8ead188c5ebd6c86bb177420842f279a1d17f4c5a9`.
Lease: `notes/progress/2026-10-19-r57-original-name-owner-trace.md` and this handoff only.

## Bounded source-owner result

For the exact input `a=forward x; z=loop x; b=forward x; z`, the source graph has four recomputed events: `ea=(Local(a),Local(forward))`, `ez=(Local(z),Local(loop))`, `eb=(Local(b),Local(forward))`, `eo=(Module(outer),Local(loop))`. Only `ez` is qualified by `loop→z→loop`. All four Apply arguments remain whole current-formal Names. The source-mode schedule does not blanket-admit all collected facts before processing; the block runs each initializer before its Install. Thus the later `eb` is not an input to the earlier recursive processing relation.

I independently inspected the source-mode execution gate, Local/Link/Name action classification, replay source union, extrusion parent retention and settlement, and per-occurrence Local capture/commit. For the changed recursive path, active Link `(N,+,L)` contributes no Apply source; `(N,−,Dz)` carries `{ez}`; replay gives `L<=Dz` with exactly `{ez}`. The signed target-2 structural traversal stops at `X2` and selected `ex2`; its complete qualified parent group is `(h_z3,h_z+,+,2)`, `(C_z3,C_z−,−,2)`, `(U_z3,U_z−,−,2)`. Settlement changes only those three copy/parent pairs. It does not reach the original forward rows.

The first Local capture writes its fresh `a` rows and its own effect route. Direct keys compose `ex<=t_a<=n_a<=r_a<=C_a<=E_a<=B` and replay adds direct `ex<=B`; no direct `r_a<=B` is claimed. The recursive group and following `z` routing do not write into the original `F0/t0/n0/r0/v0` closure. The second `b` occurrence resolves to the same installed `forward` scheme slot, root and boundary, but starts a new Local route after `a`'s completed frame was committed and removed. Its live capture includes the actual original `t0,n0,r0` rows and bounds. A distinct `mu_b` maps them to `t_b,n_b,r_b`; restoration directly inserts `(t_b,−,n_b)`, `(n_b,−,t_b)`, `(n_b,−,r_b)` using that same table before the root link. If its Apply continues, the separate `eb` comparison has `h_b<=t_b` and `r_b<=C_b`, yielding the bounded mapped scalar path through the restored bounds.

The complete source sets, signed keys, capture rows, direct restoration and successful-prefix limitations are in the two frozen R57 author outputs. My trace agrees with the independent Sol source derivation. Both are bounded constructor evidence only: not observed solver success, complete typing, termination, invocation or runtime behavior. Forwarding-preservation §§1,6–7 and Simple-sub A/B remain OPEN 0→0; R50 remains NOT ADOPTED. No production or semantic change is authorized.

This exact lease grants read-only source inspection, not a code slice; **NO_SAFE_CODE_SLICE**. Initial fresh compiler review was CLEAN. Initial spec review found one minor stale-status inconsistency in the Luna trace; the trace status is corrected below, and fresh review of the corrected Luna outputs is pending before primary adjudication. No parser, preflight, solver, test, build, runtime, probe, instrumentation, measurement, code/semantic edit, scratch output or descendant was used. Root author is not a reviewer. Requested Luna/high; observed model/effort UNKNOWN/UNKNOWN. The corrected trace and handoff are frozen at the hashes below.

## Frozen output identities

- Sol proof: `notes/theory/2026-10-19-r57-original-name-two-capture.md`, SHA-256 `9603acbd00419111821aa0e808258d5b744f5afc0b2d8601be2cc7ffd8f883ff`.
- Sol handoff: `tasks/agent-loop/inbox/20261019-r57-proof.md`, SHA-256 `3510d54cb5f5ade190833cc5657eebcf05952e1c80df8b52e6c63b9a83dc28b7`.
- Luna source-owner trace: `notes/progress/2026-10-19-r57-original-name-owner-trace.md`, SHA-256 `b61c52cc4afa02b98828df76cc8182d15a60cb5d240dde4a73085f50ae08e0ce`.
- Luna handoff: this file, SHA-256 recorded in the state receipt after this correction freeze.

State: Luna source-owner and Sol proof lanes `STOPPED / WRITES_STOPPED / NO_DESCENDANTS`; original review rounds stopped; fresh compiler/spec review of corrected Luna trace and handoff pending.

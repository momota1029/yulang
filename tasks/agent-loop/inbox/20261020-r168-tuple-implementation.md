# R168 ordered-tuple implementation design handoff

- Sprint: `ordered-tuple-construction-20261020-r168`; proposed revision 1; no lease or launch.
- Contract SHA-256: `cb33b37ce48b7b2131e56cf3c3e510c5e24ac9177f743145966abf94479b8ce8`.
- Assignment: `R168-TUPLE-IMPLEMENTATION-DESIGN`, revision 1; Luna primary.
- Baseline/source pins: contract and Luna refresh before grant.
- Objective: write an implementation design against actual syntax/HIR, solver, closed type, and runtime consumers; reconcile all exact paths with the proof matrix. Do not edit code.
- Exact outputs: `notes/design/2026-10-20-r168-tuple-extension.md` and this handoff only.
- Code leases: NONE in revision 1. A sequential contract revision must list every exact path/hash and pass prospective independent review before any code edit.
- Constraints: arbitrary finite ordered tuples per R149; no pair encoding; no destructuring; preserve Unit/Group distinctions, element type/effect order, source provenance, and left-to-right single evaluation.
- Budget: 300 seconds within 6000; no carryover. Implementation's 2700-second lane is conditional on the reviewed matrix and revised exact code leases.
- Review: `/root/r157_contract_review`, independent and fresh for the revised code boundary and final diff.

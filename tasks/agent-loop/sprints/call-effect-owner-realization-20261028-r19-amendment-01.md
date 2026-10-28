# R19 amendment 01 — disjoint proof handoffs and primary implementation accounting

Base contract: `CALL-EFFECT-OWNER-REALIZATION/20261028-r19`, revision 1.
This amendment changes only assignment ownership and exact output paths; it does
not change the original theorem, source domain, semantics, success criteria,
dependency set, or total 2,100-second sprint grant.

- Astra owns `notes/theory/2026-10-28-call-effect-owner-realization-r19.md` and
  `tasks/agent-loop/inbox/call-effect-owner-realization-r19-proof.md`.
- The `lean_prover` owns its new isolated Lean module and the distinct
  `tasks/agent-loop/inbox/call-effect-owner-realization-r19-lean.md` handoff.
- Sol's read-only source lane owns only
  `tasks/agent-loop/inbox/call-effect-owner-realization-r19-source.md`.
- Luna primary owns the implementation and integration. The primary's 1,000
  seconds includes at most 400 seconds for the exact three isolated Rust files;
  this replaces the separate 600-second primary plus 400-second implementer
  accounting in revision 1. No implementer child is dispatched.
- Fresh review remains a separate 250-second assignment after all authors stop.

The distinct handoffs prevent concurrent proof writers. Every other base
contract condition remains unchanged. Current-state revision becomes 2.

# R50 admission — known unmatched Catch operation forwarding

Date: 2026-10-31  
Sprint: `EFFECT-PERMISSION-KNOWN-UNMATCHED-FORWARDING/20261031-R50`  
Predecessor: R49 `CHANGES_REQUIRED`, outcome
`tasks/agent-loop/history/effect-permission-authenticated-residual-20261031-r49-outcome.md`.

The user’s ongoing Rust/Lean effect-hygiene goal authorizes this bounded
successor without changing semantics or production authority. The exact repair
distinguishes authenticated matching, authenticated known mismatch, and
unavailable identity. Known mismatch forwards unchanged; only a matching
operation can enter suppression authentication; missing matching evidence
remains unavailable before publication. Lean must establish the same case split
and retain complete suppression prerequisites.

Exact writer paths and budgets are in
`tasks/agent-loop/sprints/effect-permission-known-unmatched-forwarding-20261031-r50.md`.
Rust and Lean lanes are disjoint. Each is capped at 900 seconds; fresh review
after both STOP is capped at 700 seconds; primary is capped at 700 seconds;
aggregate is 3,200 seconds. No build/test/checker rerun, environment, worktree,
cache, target, scratch, or quarantined path is authorized.

The R49 Rust, Lean and handoff bytes remain frozen as the reviewed failed
submission. R49 reviewer is STOPPED; its review intake preserves the blocking
counterexample, the minor hash typo, theorem census and open boundaries. R50
will use numbered handoff revision 2 and obtain a fresh review of the repaired
bytes before any source checkpoint is staged.

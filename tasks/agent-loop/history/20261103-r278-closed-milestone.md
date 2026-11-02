# R278 closed milestone — reviewed conditional guard result

R278 closes **REVIEWED_CONDITIONAL**. Immutable contract `tasks/agent-loop/sprints/public-entry-guard-incompatibility-r278.md`, SHA-256 `26281ae2d1b6dafda3acd8b6b16a38d6541729512a14ba93b5b85777e6761233`.

Sol stage 1 charged 300 seconds; cumulative Sol charge 11,400 seconds. Fresh independent review `PASS_CONDITIONAL_ONLY`, charged 600 seconds. Luna's 300-second preparation/adjudication allocation is retained in the R278 accounting. The proposed R278 stage-2 600-second grant was never issued and is canceled; it is not transferred or charged again.

Frozen outputs:

- Theory `notes/theory/2026-11-03-public-entry-guard-incompatibility-r278.md`, SHA-256 `bc6876084151d872c08f565bd0a0bf79173e1c7902da683c811b9b44dd20b82e`.
- Handoff `tasks/agent-loop/inbox/public-entry-guard-incompatibility-r278.md`, SHA-256 `fe761f634a1c4d17a516f93112c764eb40f284ad09dfd768034e7ba38e58a27c`.
- Independent review `tasks/agent-loop/history/20261103-r278-independent-review.md`, SHA-256 `7a67c5e08cd671e9588a07abe75e8e501185568dac0f64fb8a565bdbddbc6f5f`.

The established result is only: if the same HIR has exactly one top-level Binding, `assemble` fails its first two-Binding guard with `CandidateError::Unsupported` before answer lookup or collection. The fixed source's production parse/HIR census and same-HIR root correspondence remain open. No actual source-qualified rejection or parent application. Parent/A/B remains 0→0; `Need_D`/R71 OPEN; `NO_SAFE_CODE_SLICE`.

The exact two R278 output leases and reviewer assignment are resolved and archived here; the frozen files and review hashes remain immutable. R279 becomes the active sprint under a separate contract/resource envelope.

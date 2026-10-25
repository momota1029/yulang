# Sprint PAPER-R50-PROCESS-EVIDENCE-20261026/r51

Status: RUNNING; finite process-evidence closure for the exact frozen R50 candidate. This is a new grant. R50 remains RESULT/EVIDENCE_INCOMPLETE; none of its spent time, checker calls or review allocation is returned. This packet changes no proof, theorem, definition or semantic claim.

## Exact frozen inputs

- Baseline commit: `e85eb20fd40426316790d1fb543d64b7676b58e8`.
- Candidate: `YulangClosure.PaperResumeExecution`, SHA-256 `5ab59033b0cea347144c50a5323e4dd6cb59cc6bfbdc0bffd063a4808e741935`.
- Strict audit source SHA-256 `7cc577fff482bac2674c6449b43cf89edfb04c9bc258c6bfaf3e5bed499aea3e`.
- Existing isolated root delta: exactly `import YulangClosure.PaperResumeExecution`.
- R50 dependency pins and semantic review remain as recorded in R50 r6 and review receipt `tasks/agent-loop/inbox/paper-resume-execution-r50-review.md` (SHA-256 `a1438c78a0cc2a6d5105fd07687f6b73902c0893f2257f13855b4fe2a139eaa3`). Reuse that review only for semantics; R51 does not claim new mathematical review.
- Preserve R50 raw calls and receipt unchanged, including the 1.072710997 s wall/monotonic discrepancy and unknown cause.

## Fixed work and budget

Create detached exact-baseline checkout `/tmp/yulang-r51-r50-process-evidence`. Copy only the byte-identical candidate and audit into it and add exactly the one-line root import. Verify all R50 dependency pins before execution.

At packet start, capture a single monotonic clock origin before checkout preparation. Primary active time includes checkout creation, dependency checking, native Lake preflight, all four calls, hashing, manifest/receipt writing and freeze. Primary grant: **420 active seconds, 4 Lean/Lake calls, 60 checker seconds**. Fresh read-only process-evidence reviewer: **180 seconds, zero Lean/Lake/checker/build/test/Git/network/write/descendants**. New packet aggregate: **600 active seconds, 4 Lean/Lake calls, 60 checker seconds**. Stop on any failed command, timeout, cap, pin mismatch or missing raw capture; no retry.

First run read-only `elan which lake`; record its exact argv, cwd, timestamps, exit, output bytes and SHA-256. Use the returned absolute native Lake executable for exactly these four commands from `notes/theory/lean`:

1. `<resolved-lake> --version`
2. `<resolved-lake> env lean --version`
3. `<resolved-lake> build`
4. `<resolved-lake> env lean .lake/R50Audit.lean`

Capture complete stdout/stderr, argv, cwd, UTC start/end, monotonic duration, exit, bytes and hashes for each call. Record one end-to-end primary active duration from packet-start monotonic origin through final verification-receipt freeze. Do not substitute the sum of checker calls for active duration.

## Exact Luna-owned paths

- `tasks/agent-loop/inbox/paper-resume-execution-r51-lake-resolution.txt`
- `tasks/agent-loop/inbox/paper-resume-execution-r51-primary-call-01.stdout`
- `tasks/agent-loop/inbox/paper-resume-execution-r51-primary-call-01.stderr`
- `tasks/agent-loop/inbox/paper-resume-execution-r51-primary-call-02.stdout`
- `tasks/agent-loop/inbox/paper-resume-execution-r51-primary-call-02.stderr`
- `tasks/agent-loop/inbox/paper-resume-execution-r51-primary-call-03.stdout`
- `tasks/agent-loop/inbox/paper-resume-execution-r51-primary-call-03.stderr`
- `tasks/agent-loop/inbox/paper-resume-execution-r51-primary-call-04.stdout`
- `tasks/agent-loop/inbox/paper-resume-execution-r51-primary-call-04.stderr`
- `tasks/agent-loop/inbox/paper-resume-execution-r51-primary-manifest.json`
- `tasks/agent-loop/inbox/paper-resume-execution-r51-primary-verification.txt`
- `tasks/agent-loop/inbox/paper-resume-execution-r51-review.md`
- `tasks/agent-loop/inbox/paper-resume-execution-r51-integration.md`
- `notes/theory/lean/YulangClosure/PaperResumeExecution.lean`
- `notes/theory/lean/YulangClosure.lean`

The reviewer checks only the new executable provenance, exact raw captures, clock/budget evidence, hashes and unchanged root delta, and independently confirms the old semantic CLEAN receipt hash. A CLEAN result plus Luna adjudication permits Luna to copy the same candidate and add the same one-line root import in the main worktree, run the required static `python3 tools/agent_sprint.py check`, and write the integration receipt. Any source byte or import delta change invalidates this packet. No question bundle may be staged or changed.

The two user-withdrawn question bundles remain `WITHDRAWN_BY_USER`, with no answers or semantic adoption. All eight legacy reservations stay quarantined. Full-owner freshening/lifetime, full-state/source/native, handlers/effects, whole executor, inference A/B and production remain OPEN.

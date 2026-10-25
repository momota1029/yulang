# Sprint PAPER-EMPTY-OWNER-RESUME-20261026/r50 (contract revision 6)

Status: RESULT — semantic review CLEAN, process evidence incomplete, integration not accepted. Revision 6 records the primary verification discrepancy, independent review disposition, and conservative stop at the existing aggregate active-work boundary. It changes no theorem, semantic claim, source authority, baseline, or question status. Contract revision r6 supersedes r5 only for this adjudication.

## Frozen outcome

The worker candidate built and passed its strict 18-declaration audit. Primary call03 default root build and call04 strict audit also exited 0. Fresh independent compiler_referee review found the bounded empty-owner proof semantically CLEAN: Q and A remain distinct; both responses use the same immutable saved continuation and operation instance; R49 prefix/erasure application is direct; no freshening assumption was introduced; all 18 public theorem types and axiom lists match the audit source. No source or proof correctness finding was reported.

The primary process receipt has a minor but unresolved evidence finding. Its commands were bare `lake --version`, bare `lean --version`, `lake build`, and `lake env lean .lake/R50Audit.lean`. The governing Lean skill requires read-only native Lake resolution and obtaining Lean's version through that Lake executable's `env lean --version`. A later read-only `elan which lake` returned `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake` (SHA-256 `8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1`), but this later lookup does not establish which executable historical calls resolved to. No `lake env lean --version` call was captured.

The primary call03 UTC timestamps span 34.257784 s while its monotonic duration is 33.185073003 s, a 1.072710997 s discrepancy. Its cause is UNKNOWN; no clock-step explanation is adopted. Preserve all original raw call files and receipt unchanged.

The worker's complete active duration is UNKNOWN, so charge its full 1200 s grant. The primary's full 420 s grant is charged because no complete active-time receipt covers preparation and recording; 35.838434179 s is only the sum of its four checker calls. The review grant is conservatively charged at 180 s because exact active duration is not available. These reservations consume the 1800 s aggregate active-work envelope. The corrected native-Lake verification is therefore not run in R50. Do not infer permission or remaining active time from the unspent 4 aggregate calls or 107.384641759 checker seconds.

R50 is not integrated or DONE. Keep the candidate frozen in `/tmp/yulang-r50-empty-owner-resume` and `/tmp/yulang-r50-empty-owner-primary`; remove primary's unintegrated copies from the shared main worktree. The existing main-worktree root remains unchanged. Any corrected verification requires a separately authorized finite packet with new active-time evidence and exact process-output leases.

The two user-withdrawn question bundles remain `WITHDRAWN_BY_USER`; no answers or semantics were adopted. Their proof/authority gaps remain OPEN. Eight legacy reservations remain quarantined. Full-owner freshening/lifetime, full-state/source/native, handlers/effects, whole-executor, inference A/B, and production remain OPEN.

## Evidence references

- r5 contract: `tasks/agent-loop/sprints/paper-empty-owner-resume-r50-r5.md`, SHA-256 `9b5755f6ee4bc5f4974094679b56dcc6607aa346a78f2c8d01867d7baab14c5b`.
- Candidate SHA-256 `5ab59033b0cea347144c50a5323e4dd6cb59cc6bfbdc0bffd063a4808e741935`; audit SHA-256 `7cc577fff482bac2674c6449b43cf89edfb04c9bc258c6bfaf3e5bed499aea3e`.
- Primary verification receipt SHA-256 `6cb07a3df1224e53ceabcb4ff818aa9d99a4cb4c74476fc81baaa7c4341b5e70`; all four complete primary stdout/stderr pairs remain byte-frozen under their r5 leases.
- Fresh compiler_referee review receipt: `tasks/agent-loop/inbox/paper-resume-execution-r50-review.md`.

Revision 6 is a result adjudication only. It authorizes no checker call, source change, root import, or integration.

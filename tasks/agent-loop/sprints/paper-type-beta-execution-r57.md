# Sprint PAPER-TYPE-BETA-EXECUTION-20261026/r57 — corrected root import and exact audit

Status: ASSIGNED. Primary-owned verification continuation after R56 stopped at root import placement. Target branch `yulang3`; exact baseline `fa776ddb531576a2cee4b0ae223aefbc254e1882`. Candidate remains byte-identical SHA-256 `0a1834040a0201c0c472f66138f6501094f7138dd3614f2bc4439a8be0cda1c8`. R55 and R56 remain FAILED and are not retried or reclassified. Preserve any external proof arrival immutably; verify provenance, full source/hash, exact claim and complete audit before adoption. If the candidate path exists with different bytes, stop.

## Goal, exact scope and success gate

Verify the unchanged manuscript type-application beta preservation candidate in a fresh isolated copy at `/tmp/yulang-r57-yulang3-type-beta-audit`. The candidate must be copied byte-for-byte. Add exactly one temporary import to `YulangClosure.lean` inside its leading import block, immediately after `import YulangClosure.PaperResumeExecution` and before the first command. Confirm the import is at the beginning and the root diff is exactly this line.

Run the complete exact-name audit for 26 public and 8 private declarations. For private declarations, construct exact `Name`s with pinned `Lean.mkPrivateNameCore` and module `YulangClosure.PaperTypeBetaExecution`, generate identifier syntax directly from each `Name`, and use that same exact name for environment lookup, theorem-kind validation, `#check`, `#print axioms`, and `Lean.collectAxioms`. Require 34 unique expected declarations, all theorem declarations, complete begin/end records, exactly 34/34, and no axioms outside `{propext, Classical.choice, Quot.sound}`. Preserve full types and axiom output.

Four literal native calls, in order: resolved native Lake `--version`; same Lake `env lean --version`; default root `lake build`; strict 34-name audit. Use pinned `-j1 -M1024`, one Lean thread. Capture exact executable/argv/cwd/exit/monotonic duration and complete stdout/stderr plus SHA-256. Any pin mismatch, first failed command, capture gap, timeout or resource cap stops the sprint; no retries or extra Lean/Lake calls. No tests.

Only after all four calls pass and every artifact is frozen, assign one fresh eligible independent `compiler_referee` for 180 seconds and zero checker calls. Reviewer checks exact candidate bytes, root inclusion, all 34 declarations and output against the original claim and R55 handoff, including `PaperValueTyped.subst_explicit`, `typeBetaValue` preservation, distinct beta-then-force `force_typeBeta_delay`, arbitrary shared contexts, distinct types, nested forall/mu and formal-binder template bodies. Any non-CLEAN result blocks integration. This bounded represented theorem does not close source/native realization, full executor, inference A/B or production.

Only after CLEAN review may Luna integrate the byte-identical module and one root import in the shared `yulang3`, record adjudication/outcome/current state, inspect exact staged paths and non-forced push. Recheck `origin/yulang3`; if it advanced, stop before push and preserve external commits intact.

## Frozen authority and inputs

Original source and parent mapping: `tasks/agent-loop/inbox/paper-type-beta-r55.md` (frozen R55 handoff); manuscript `docs/yulang-operational-type-safety-ja.tex`; correction `notes/theory/2026-10-24-corrected-core-value-continuation.md`. Preserve original statements, quantifiers, constructors and meanings. Do not read, answer, adopt or edit withdrawn semantic questions.

Candidate source is `/tmp/yulang-r55-type-beta-finalize/notes/theory/lean/YulangClosure/PaperTypeBetaExecution.lean`, SHA-256 above. R56 exact-name audit source SHA-256 `3056fded75008665f893c26bf6485cdd2672e1e14683631a813ad10bc3102cb7`; reuse its source unchanged only after verifying this digest. Root import placement must be corrected as specified. Revalidate all R56 dependency/toolchain/manuscript/Lean-library pins in the R56 contract and R55 handoff against the isolated baseline before native call 1. Native Lake: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`, expected SHA-256 `8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1`; expected Lean 4.35.0.

## Budget, ownership and receipts

Fresh fixed budget: primary 420 elapsed seconds, 4 native calls, 90 checker seconds; fresh reviewer 180 elapsed seconds and zero checker calls; total 600 elapsed seconds, 4 calls, 90 checker seconds. Primary origin UTC `2026-10-25T22:31:11.959580Z`, monotonic `48729098930805 ns`; charge setup, pin checks, calls, freeze, review and any permitted integration from this origin. No transfer from R55/R56.

Primary isolated writes only under `/tmp/yulang-r57-yulang3-type-beta-audit`: copied candidate; one-import root copy; `.lake/R57Audit.lean`; handoff `tasks/agent-loop/inbox/paper-type-beta-r57-yulang3-primary.md`; origin/artifact/call manifests and complete `.stdout`/`.stderr`; isolated Lake config/cache. Shared branch pre-gate writes: this contract and `current.json`. After CLEAN review, exact source/root integration and primary/review/outcome/current receipts. Reviewer writes only `tasks/agent-loop/inbox/paper-type-beta-r57-review.md`. All raw outputs are immutable after freeze. Keep unknown legacy leases quarantined and do not overlap their paths.

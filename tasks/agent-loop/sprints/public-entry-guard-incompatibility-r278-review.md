# R278 independent review — conditional guard incompatibility

Status: CANDIDATE until reviewer contract gate, Luna GO and resume acknowledgement.
Reviewer: `/root/r276_production_entry_clean_review`; requested compiler_referee, `gpt-6.1-sol/medium`. Reviewer did not author R278.
Original parent/source domain/semantics unchanged. Parent/A/B 0→0; `Need_D`/R71 OPEN; `NO_SAFE_CODE_SLICE`.

## Frozen target and review question

Review only this bounded claim: from the authenticated R277-E001 production body, does `assemble` first require exactly two `HirItem::Binding`s and no `Expression`, and does the conditional `H_count` (the actual argument HIR has exactly one top-level Binding `outer`, while nested bindings are local-source contents) force that first guard to return `CandidateError::Unsupported` before reading `answer` or entering collection?

Do not treat `H_count` as an established source fact. Independently reconstruct the guard from the pinned source payload **before reading either producer output**. Then inspect the frozen theory and handoff to decide whether they accurately state (1) the source-derived guard condition, (2) only conditional carrier incompatibility, and (3) the missing source-to-shape edge. Exact witness rejection is not claimed. Distinguish a parse/lowering exit from an `assemble` rejection.

Review outcomes: `PASS_CONDITIONAL_ONLY`; `INCOMPLETE` with exact missed premise/defect; or `MAJOR_DEFECT` if the bounded guard/ordering claim is wrong. A pass certifies no actual source-to-shape implication, no accepted-source rejection, no compiler behavior outside this public experiment and no parent theorem.

## Exact pins and read order

Contract-only gate: hash this review contract and `tasks/agent-loop/history/20261103-r278-review-admission.md` only. Return a current-session WAITING acknowledgement and do not read technical sources or producer outputs. Luna then supplies an immutable GO and asks for fresh resume acknowledgement.

After GO, first match these pins sequentially without displaying producer output:

- R278 review contract: supplied in this contract's admission/GO records.
- R278 main contract `tasks/agent-loop/sprints/public-entry-guard-incompatibility-r278.md`: SHA-256 `26281ae2d1b6dafda3acd8b6b16a38d6541729512a14ba93b5b85777e6761233`.
- R278 stage-1 GO `tasks/agent-loop/history/20261103-r278-stage1-go.md`: `25bf8e487ba93687ec9576e198b578677b94d83480a1fb9e5db7c7ee32fdaec6`.
- R278 stage-1 STOP `tasks/agent-loop/history/20261103-r278-stage1-stop.md`: `8e7fba7945a8c63663e38f1b6558ab4646d7747c02fa01020e6ff11bb0ba77da`.
- R277 source view/index/ranges: `ebeae02540be5811850017b6f8b7ff49783a95e17d2b05358a155bd47bb22b21`, `8fb7a74c4953d0f78e04f321f437432bbdb9baae811027c555854ade06bfa0da`, `63f2ce9d1ffb2e14a497d89b928065edd955f3ecd2266b0eb51f670fabd4e855`.
- R277-E001 exact interval: `crates/yu-solver/src/candidate_receiver.rs:2921–3179`, whole-file SHA-256 `5ca308e7b890e57a8458a151554ece55585d762565204d39c520c4b534e44ade`, excerpt SHA-256 `38aeae41a76d3f85107559a60e5e6553aa19ad935917502eb78582162c1b557d`.
- Frozen R278 theory: `notes/theory/2026-11-03-public-entry-guard-incompatibility-r278.md`, SHA-256 `bc6876084151d872c08f565bd0a0bf79173e1c7902da683c811b9b44dd20b82e`.
- Frozen R278 handoff: `tasks/agent-loop/inbox/public-entry-guard-incompatibility-r278.md`, SHA-256 `fe761f634a1c4d17a516f93112c764eb40f284ad09dfd768034e7ba38e58a27c`.

Open only the R277-E001 production interval as technical source. Reconstruct the guard independently before opening the R278 theory or handoff. No other source body, prior producer output, fixture text, test body, or caller search is needed or authorized. The 87-byte witness may be referenced only as contract-level context; it does not supply `H_count`.

## Resource and restrictions

Fresh independent review grant: 600 seconds total including pin and resume gates, charged in full when issued. No extension, reset or refund. Requested `gpt-6.1-sol/medium`; observed model/effort remain UNKNOWN unless actually reported. No code writes, tests, builds, probes, Cargo, Lean, runtime execution, external paths, descendants or scratch/cache files. Reviewer writes no repository file; Luna records the receipt. Stop immediately on pin mismatch or read-boundary failure.

Review only R278 stage 1. Stage 2 has no authority yet. After independent review, Luna adjudicates and consults the dispatcher about the next bounded step. Even a clean pass leaves the source-to-shape bridge unproved, Parent/A/B 0→0, `Need_D`/R71 OPEN and `NO_SAFE_CODE_SLICE`.

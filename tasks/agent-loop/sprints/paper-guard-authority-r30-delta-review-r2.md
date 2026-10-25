# Sprint PAPER-GUARD-AUTHORITY-DELTA-REVIEW-20261026/r2 — fresh M1 review of typed discriminators

Status: FROZEN; admitted by Luna for one fresh, bounded review packet.

Branch: `research/simple-sub-intrusion`

Baseline: `8e8f6c1ac`

Contract revision: r2.

## Objective

Independently review the repaired R30 constructor-authority report after the r1
M1 found two MAJOR evidence defects. Check whether each concrete finite heap
claimed as typed has valid node-by-node derivations under the pinned manuscript
rules, whether conditional recursive-type instances stay conditional, whether
unsupported instances are explicitly called unestablished, and whether the
polymorphic two-node graph correctly applies the type-application and fresh
abstraction rules. Also recheck constructor inventory, `both` derivation
retention, adapter/code distinction, and HigherOrder separation.

This is a source/authority review only. The open guard rule and all parent
gates remain OPEN. The reviewer must distinguish an unestablished witness from
an impossible witness, a typed cycle from its missing guard classification,
and a conditional recursive-type derivation from an admitted paper instance.
No semantic choice or production promotion is authorized.

## Frozen dependencies

- R30 source contract: `tasks/agent-loop/sprints/paper-guard-constructor-authority-r30-r1.md`, SHA-256 `77d1512967f84808ea7bffe1a488e3b2d34b4aaa50ea3475a3753aa99236a3b6`.
- Revised primary report: `tasks/agent-loop/history/paper-guard-constructor-authority-r30-primary-r2.md`, SHA-256 `6fdaa99e5e4eaa11fd021e4416c9b2ff039799b3ff7ef911900850b313ceb469`.
- R31 M1 finding: `tasks/agent-loop/inbox/paper-guard-authority-r30-delta-review.md`, SHA-256 `a2e52ef7b65ae5edf64d11e8d0523ec212da9b7e9e8eacb6379029336f81770d`.
- R31 review-only contract: `tasks/agent-loop/sprints/paper-guard-authority-r30-delta-review-r1.md`, SHA-256 `87070d035973806cf702222d389bc06af0a2366d1f2d689f419f0a57471b8b71`.
- R30 source handoff: `tasks/agent-loop/inbox/paper-guard-constructor-authority-r30-research.md`, SHA-256 `6c1717c0de5861d6e14c0a931af60bee8d10866546ca2fd76a06b57ecea800a6`.
- R30 first M1: `tasks/agent-loop/inbox/paper-guard-constructor-authority-r30-review.md`, SHA-256 `988d6745de5a272c8bc39bdf655f39b02573991954992c7b24898a9c15f5770f`.
- Operational manuscript: `docs/yulang-operational-type-safety-ja.tex`, SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- Source manuscript: `docs/yulang-source-type-safety-ja.tex`, SHA-256 `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`.
- Raw syntax: `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`, SHA-256 `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`.

Any dependency byte change invalidates this target and returns it to Luna.
The reviewer did not author the source handoff, prior reviews, or revised report.

## Sole review lane

One fresh registered nonauthor M1 `spec_auditor` reviews the frozen primary
snapshot and pinned sources. It may write only
`tasks/agent-loop/inbox/paper-guard-authority-r30-delta-review-r2.md`. If its
read-only boundary prevents writing, it returns the complete report and Luna
persists that exact text. No descendants or other worker lanes.

## Budget and permissions

- Total cap: 180 active seconds: primary launch/intake <=30 seconds and fresh
  reviewer <=150 seconds. The previous R31 grant remains consumed; no transfer,
  renewal, or budget reuse.
- Reviewer source reads, hashing, and clock reads only. Zero checker,
  Lean/Lake/cache, Rust, build, test, runtime, benchmark, network, or Git calls.
- One process, one CPU, 1 GiB RAM, and 120 seconds per process. No code,
  semantics, manuscript, or source edits.
- Record start time before launch. If cumulative duration or cessation is
  unknown, charge the full reviewer grant and stop. Stop if a pinned byte
  changes, the reviewer is unavailable, or a semantic/authority decision is
  required.
- Implementation: `NO_SAFE_CODE_SLICE`.

## Review and integration boundary

A clean result closes only the two bounded review-artifact findings and
confirms this exact source characterization. It does not close the source
paper guard theorem or any parent. Luna adjudicates, synchronizes compact
current state, then consults the dispatcher at the packet boundary. Any
remaining major stays OPEN and requires another separately admitted packet.

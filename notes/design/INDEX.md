# Design authority index

This index is a navigation aid. The listed source document remains authoritative for its own text and scope. If this file conflicts with a source, read the source and correct the index.

| Document | Status | Authority scope | Approved / state | Useful locator or gate |
|---|---|---|---|---|
| `docs/yulang3-architecture.md` | Authoritative | Yulang3 compiler architecture, phases, runtime direction, testing/CI and cache principles | user-approved 2026-08-18 | §4.2.2 parser recovery/header discovery; §6.9 state-slot decision; §8.3 native + Perceus decision |
| `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` | Authoritative | `yu-syntax` chasa grammar, AST/direct-CST ownership, recovery, dispatch and declaration addenda | user-approved addenda recorded in the document and task history | Navigate by named `FOO-G/J/T/R` and gate headings; do not read 1.7 MB indiscriminately |
| `notes/design/2026-08-20-phase2-parser-fixture-schema.md` | Authoritative | Phase 2 parser compatibility fixture product and observed parser/recovery contract | Authoritative; population/open questions continue separately | Problem statement and fixture schema sections |
| `notes/design/2026-08-30-declaration-module-split-plan.md` | Authoritative, completed | Mechanical module topology and visibility for splitting `declaration.rs`; zero behavior change | user-approved 2026-08-30; P1–P14 completed at `a4b98643` | 17-commit plan; no active implementation gate remains |
| `notes/design/2026-08-30-codex-only-orchestration-migration.md` | Authoritative, implemented | `yulang3` agent orchestration, design authority, durable rules, testing/incident placement | approved 2026-08-30; implementation prepared for PR merge | §14 four-commit migration plan |
| `notes/design/2026-08-30-codex-only-orchestration-approval.md` | Authoritative approval record | Status transition for the migration plan above | approved 2026-08-30 | Supersedes the plan's original Proposed header and implementation gate |
| `notes/design/2026-08-30-codex-only-orchestration-migration-report.md` | Implementation report | Scope/configuration/legacy audit for the migration | 2026-08-30 | Commit sequence, verification gate, deferred work |
| `notes/design/2026-08-30-declaration-companion-with-addendum.md` | Authoritative | Shared declaration-owned `with:` grammar/CST/AST/recovery for Struct/Type/Enum/Error/Act | user-approved 2026-08-30 after independent compiler/spec/performance review | DC-G/J/T/R; owner matrix; Gates 1–6 complete, Gate 7 next |
| `notes/design/2026-08-30-declaration-companion-gate2-recovery-amendment.md` | Authoritative | Gate 2 shared canonical Statement malformed-run recovery; permits one comment-atomic ordinary recovery correction | user-approved option 1 on 2026-08-30 | Canonical scanner contract and Gate 2 rollback/verification exception |
| `notes/design/2026-08-30-declaration-companion-gate2-performance-amendment.md` | Authoritative, completed | Gate 2 semantic-work performance gate and bounded verification after two whole-process rollbacks | user-approved 2026-08-30 after independent performance/spec review; Gate 2 completed 2026-08-30 | Supersedes only the enumerated Gate 2 performance/reviewer clauses |
| `notes/design/2026-08-31-declaration-companion-gate3-nud-sink-amendment.md` | Authoritative, completed | Gate 3 generic speculative NUD candidate ErrorSink transaction correction | user-approved option 1 on 2026-08-31; Gate 3 completed 2026-08-31 | Exactly one checkpoint/rollback pair in `expression_nud_candidate_input`; bounded focused/package verification |

## Index maintenance

For a new design, record path, status, authority scope, approval date, supersession, and the smallest useful section/gate locator. Do not copy the full decision into this index. Mark completed implementation gates without deleting the design history.

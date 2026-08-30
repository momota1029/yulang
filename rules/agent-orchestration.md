# Codex-only agent orchestration

Yulang uses a primary Codex agent for user interaction, authority resolution, task classification, review adjudication, and git integration. Repository exploration, design, implementation, and independent review are separated by role.

## Primary responsibility

The primary agent:

1. identifies the user objective and current branch;
2. reads the minimum task/design context;
3. classifies authority, behavior, scope, performance, and surface;
4. selects roles and defines their inputs, write permission, stop condition, and required output;
5. keeps independent reviewer reports isolated until all are complete;
6. checks findings against repository evidence and authority;
7. records accepted findings and delegates repairs to a fresh implementer;
8. owns staging, commits, PRs, pushes, and final reporting;
9. presents only genuine unresolved user decisions.

The primary agent's reread is useful for integration but does not count as independent review. A producer's self-review never counts.

## Roles

| role | mode | responsibility |
|---|---|---|
| built-in `explorer` | read-only | map files, symbols, entrypoints, call paths, and current state |
| `architect` | read-only | new/cross-layer design, invariants, gates, rollback and decisions |
| `implementer` | workspace-write | implement confirmed design or accepted findings |
| `compiler_referee` | read-only | adversarial semantics, root cause, soundness and invariant review |
| `spec_auditor` | read-only | exact design/spec/test-contract conformance |
| `regression_auditor` | read-only | sibling paths, public surfaces, fixtures, diagnostics and parity |
| `performance_auditor` | read-only | work, allocation, cache, parallelism and resource risk |
| `docs_writer` | workspace-write | confirmed public documentation under artifact style rules |

Model and effort are fixed in `.codex/agents/*.toml`. Do not route active work using legacy Level numbers, Fable/Sonnet availability, or ad hoc Sol/Terra/Luna tier prose.

## Task classification

Before a write, classify:

| axis | values |
|---|---|
| authority | `none / existing / new-decision` |
| behavior | `none / intended / uncertain` |
| scope | `local / cross-layer` |
| performance | `cold / hot / unknown` |
| surface | `internal / public / docs` |

`architect` is mandatory when:

```text
authority = new-decision
OR behavior = uncertain
OR scope = cross-layer
```

Do not reopen an existing Authoritative gate when it already determines the implementation. Re-enter design only for a concrete contradiction, false premise, missing decision, or scope expansion.

## Routing matrix

| task | pre-write | writer | mandatory independent review |
|---|---|---|---|
| file/symbol/current-state lookup | primary or built-in `explorer` | — | — |
| read-only root-cause investigation | `explorer`; open-ended design question to `architect` | — | difficult semantics may require `compiler_referee` |
| typo/format/fully specified rename | — | `implementer` | `regression_auditor` |
| existing Authoritative gate | — | `implementer` | `spec_auditor` + `regression_auditor` |
| pure refactor/module split | `architect` only if no sufficient design exists | `implementer` | `spec_auditor` + `regression_auditor` |
| bug fix | `explorer`; `architect` if cause/owner remains unclear | `implementer` | `compiler_referee` + `regression_auditor` |
| parser grammar/recovery/CST/AST | unresolved decision: `architect` + user approval | `implementer` | `compiler_referee` + `spec_auditor` + `regression_auditor` |
| HIR/type/core semantics | `architect` + user approval | `implementer` | `compiler_referee` + `spec_auditor` + `regression_auditor` |
| public API/language behavior | `architect` + user approval | `implementer` | `compiler_referee` + `spec_auditor` + `regression_auditor` |
| performance optimization | `explorer` → `architect` | `implementer` | `performance_auditor` + `compiler_referee` + `regression_auditor` |
| expected output/snapshot/golden | pre-write `spec_auditor` | `implementer` | `regression_auditor` |
| new/changed design document | `architect` | primary records reviewed draft | `compiler_referee` + `spec_auditor`, then user approval |
| web/docs or README | `spec_auditor` when semantics/examples are involved | `docs_writer` | `spec_auditor`; executable examples also `regression_auditor` |
| repository/orchestration rule | primary or `architect` | primary | fresh `spec_auditor` |

## Information boundaries

### Producers

`implementer` and `docs_writer` receive confirmed scope, governing source, accepted findings, and direct dependencies. They do not receive permission to resolve unspecified decisions. They do not certify their work.

### `compiler_referee`

Reads target code, direct dependencies, authoritative source, and relevant tests. For initial review, do not provide the implementer's defense or success claim.

### `spec_auditor`

Reads exact governing design/spec, target diff, and test contract. Does not treat implementation convenience or current output as authority.

### `regression_auditor`

Reads before/after, public call sites, sibling cases, fixtures and diagnostics. Does not assume stated zero-behavior-change claims.

### `performance_auditor`

Reads changed path, call frequency, loops/worklists, ownership and measurements. Does not treat the producer's performance claim as evidence.

Reviewer reports remain isolated until all reviewers finish. Independent read-only reviews may run in parallel. Write-capable roles never run concurrently in the same working tree.

## Findings and repair loop

Use severities:

- `BLOCKING`: invalid semantics, missing authority/input, unsafe operation, or an unexecutable rule prevents continuation.
- `major`: hidden assumption, wrong owner, contract deviation, likely regression, or substantial performance/resource risk.
- `minor`: local clarity, naming, organization, or low-risk coverage issue that does not change correctness.

The primary agent verifies each finding and records accepted/rejected status with reason. A fresh `implementer` repairs accepted findings. A fresh reviewer verifies the repaired artifact. Do not let a reviewer edit its own finding.

Completion requires no accepted `BLOCKING` or `major` finding in the latest required review round, and no artifact change after that round except review-record updates.

## Expected-output gate

Before changing a snapshot, golden, fixture expectation, diagnostic expectation, semantic `assert_eq!`, or test name, `spec_auditor` determines whether the current expectation is authoritative and whether a user-approved spec change exists. Current implementation output is never sufficient reason.

## Performance trigger

`performance_auditor` is required for new/changed traversals, nontrivial allocations or clones, caches/invalidation, table/index rebuilds, inner-loop branches, recursion/worklists, parallelism/locking/thread counts, benchmark-motivated code, or potentially heavy verification commands.

## Handoff contract

Every specialist report uses concise technical English and includes:

- role and mode;
- objective and scope inspected;
- governing authority/rules;
- findings or files changed;
- exact checks/commands and results;
- uncertainty and omitted scope;
- blocker or decision point;
- recommended next role/action.

Subagents do not stage, commit, push, reset, rewrite history, or ask interactive permission questions.

## Design workflow

A new durable decision follows:

```text
architect draft
→ independent compiler/spec review
→ primary adjudication
→ user approval
→ Authoritative record
→ implementer gates
→ independent review after each required gate
```

Authorship/model identity is provenance only; `rules/design-authority.md` controls authority.

## Deterministic checks and hooks

Builds/tests are evidence, not reviewer roles. V1 defines no automatic repository hooks. Use focused safe checks under `rules/testing.md`; design a shared safe verifier separately before automating broad commands.

## Git integration

Follow `rules/git-concurrency.md`. The primary stages explicit paths and creates coherent commits after checking scope and concurrent work. The `yulang3` policy does not authorize changes to frozen `main`.

# Codex-only orchestration migration implementation report

- Status: Implemented; merge gate is repository review and CI
- Date: 2026-08-30
- Base: `yulang3` at `167f7f7890a58029200d95639c3eea6a85b5fcfd`
- Implementation branch: `codex-only-orchestration`
- Governing design: `notes/design/2026-08-30-codex-only-orchestration-migration.md`
- Approval: `notes/design/2026-08-30-codex-only-orchestration-approval.md`
- Compiler behavior: intended zero change

## Commit sequence

1. `fe67308e98f3a1d4f617b6c00704b6049dbbab5e` — extract durable rules, design index, and historical incidents.
2. `310dee28fc4dcc765e84ab415e2e705b5cc58b2a` — add project-scoped Codex roles and orchestration contract.
3. `ec75babd46356540f9b5adf5cb6948516e9b58c1` — switch active root policy and retire Claude-only files atomically.
4. The commit containing this report — close legacy terminology and residual-reference audit.

## Scope audit

The branch changes policy, configuration, design navigation, and incident records only.

- No file under `crates/`, `benchmarks/`, `web/`, `spec/`, or test/fixture directories is changed.
- `Cargo.toml`, `Cargo.lock`, and `.github/workflows/core.yml` are unchanged.
- No expected output, snapshot, fixture, diagnostic, or public documentation prose is changed.
- `.codex/hooks.json` is intentionally absent.

## Configuration audit

- Primary configuration: `gpt-5.6-sol`, `high`.
- Spawned-thread cap: six, excluding the primary.
- Seven custom roles exist with required `name`, `description`, and `developer_instructions` fields.
- `architect` and `compiler_referee` use Sol/high/read-only.
- `spec_auditor`, `regression_auditor`, and `performance_auditor` use Terra/high/read-only.
- `implementer` uses Sol/high/workspace-write.
- `docs_writer` uses Terra/high/workspace-write.
- Reviewers are read-only; only the two producer roles are write-enabled.

The field layout follows the current Codex custom-agent schema. The TOML is deliberately simple and contains no MCP server, hook, skill, or transport-specific configuration.

## Active-policy audit

- `CLAUDE.md` is removed.
- `.claude/settings.local.json` is removed; the empty directory disappears from the tree.
- Root `AGENTS.md` is limited to purpose, authority/routing pointers, hard invariants, primary responsibility, communication boundary, and final verification.
- Active routing no longer depends on Level 1–4, Fable/Sonnet availability, or dynamic model-tier prose.
- Subagents are explicitly forbidden to stage, commit, push, reset, stash the whole tree, or rewrite history.
- Design authority derives from user approval and declared scope.
- Historical model names remain only as provenance, incidents, quotations, negations, or the compatibility layer.

## Verification gate

Before merge, compare the branch against `yulang3`, inspect the changed-file list, and run the repository's existing PR CI baseline:

```text
cargo fmt --check
cargo xtask check-graph
cargo check --workspace
```

A full test run is not required for this policy-only migration and would not add a relevant compiler-behavior signal. CI and PR review results remain GitHub records rather than being copied into this design report.

## Deferred work

The following remain separate tasks by design:

- shorten `tasks/current.md` into a navigation file;
- design and implement a safe `cargo xtask verify` entrypoint;
- expand focused/nightly CI testing;
- add resource monitoring or hooks;
- add precise locators for every section of the large parser architecture document.

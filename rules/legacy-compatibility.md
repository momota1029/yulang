# Legacy orchestration terminology

This compatibility layer applies to historical design documents, progress notes, task histories, commit messages, and incident records created before the Codex-only migration. It prevents stale model names from becoming active policy.

## Active policy boundary

Current operation is defined only by root `AGENTS.md`, `.codex/config.toml`, `.codex/agents/*.toml`, and `rules/`.

The following historical phrases are not active instructions:

- `Codex MCP first`, MCP request templates, codex-flow fallback, and MCP capability checks;
- Claude-as-supervisor / Codex-as-worker transport rules;
- Fable 5 availability or Sonnet 5 substitute procedures;
- Level 1–4 or ad hoc Sol/Terra/Luna routing prose;
- Codex-commits / Claude-pushes responsibility splits;
- Gemini as the final policy-compliance judge.

Do not revive them from git history, old task notes, or quoted incidents.

## Role interpretation

When an old operational note must be interpreted rather than merely read historically:

- `Claude` acting as user-facing supervisor, adjudicator, or pusher maps to the primary agent.
- `Codex` acting as code writer maps to `implementer`.
- `Codex` acting as an exhaustive rule/spec checker maps to `spec_auditor` or `regression_auditor` according to the question.
- an adversarial semantic/proof/correctness reviewer maps to `compiler_referee`.
- an architectural author or Fable-design role maps to `architect`.
- a performance/resource reviewer maps to `performance_auditor`.
- a public prose author maps to `docs_writer`.

Choose the current role from task responsibility, not from the historical model label.

## Design provenance

Old signatures remain untouched. A legacy document is authoritative only because it records user approval within a declared scope, not because Claude, Fable, Sonnet, Codex, Gemini, or another model authored or reviewed it.

The approval record `notes/design/2026-08-30-codex-only-orchestration-approval.md` supersedes the migration plan's original `Status: Proposed` header and implementation gate. The plan content itself remains unchanged.

## Historical text audit

Occurrences of legacy names are allowed when they are:

- quotations;
- authorship/review provenance;
- dated incident descriptions;
- old commit or gate history;
- explicit negations or compatibility explanations in active rules.

They are not allowed as a live command, permission model, routing rule, authority condition, or git responsibility split.

When uncertain, check whether the sentence asks a current agent to do something. If so, convert the responsibility to the current role model or remove the obsolete transport instruction.

# Proof and task-decomposition role delivery

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Inspected remote baseline: `6bb5c314af7cb62da762a0198417629fb4273e17`
Status: role policy independently reviewed; prover registration and live custom-role launches verified, including observed Sol/high runtime metadata

## Scope and authority

The user explicitly requested GPT-6.1 Sol proof and task-decomposition roles,
with bounded proof parallelism and escalation to Astra. The
[workflow decision](../design/2026-10-10-proof-and-task-decomposition-roles.md)
records that authority. This is an M2 bounded orchestration-contract change:
one independent conformance reviewer covers role/model routing, descendant
budgets, lease lifecycle and review isolation. No compiler, semantic, theorem-
status, production adoption or expected-output changes are in scope.

The isolated review checkout's policy/configuration blobs match the inspected
remote baseline. The two shared metadata files were refreshed exactly to that
baseline before adding only workflow navigation. Other worktrees and their
uncommitted research artifacts were not modified.

## Changed responsibilities

- New `prover`: normal Sol/high via existing defaults; no role model/effort
  pins, preserving a real native Astra override path. Proof coordination needs
  a primary-issued packet and has at most two leaf workers with no redelegation.
- New `task_decomposer`: pinned Sol/medium, read-only, concrete packets and
  critical path; neither scheduling nor recurring plan churn.
- Existing `researcher`: complementary falsification/experiment/source work.
- Root routing, research budgets, assignment seed and Git lease rules use the
  same narrow delegation exception. Existing primary/specialist model pins,
  global thread ceiling, independent-review and primary-integration duties remain.

## Validation record

The primary's focused Python validation passed: all 12 TOML files parse, all
11 role identities and required fields are valid, existing model/effort/sandbox
pins and primary configuration values are preserved, the proof default and
unpinned Astra override route are consistent, and decomposition is Sol/medium
with a read-only sandbox. Eight added local links/anchors resolve. The exact
14-path scope matches the intended change; `git diff --check` passes. All
pre-change blobs match the inspected remote baseline, including the exact
refreshed task/index files.

Fresh independent GPT-6.1 Sol reviewer `role_policy_review` reported no
BLOCKING, major or minor findings across model resolution, role format,
one-generation delegation, aggregate budgets, interruption/lease lifecycle,
primary authority, independent review, fallback and concrete proof work. The
reviewer separately parsed the 12 TOML files. Subsequent changes only filled
review/status records; no functional repair was required.

Zero Cargo builds, benchmark processes or broad compiler tests ran: compiler
behavior is unchanged. The project config now registers `[agents.prover]`
through `config_file = "agents/prover.toml"`; the standalone role file by
itself was not enough for discovery. Codex CLI accepted the project config in
strict mode and launched real `prover` subagents for a bounded PUSH-count
lemma and a fresh construction of the nested Function-polarity and exact
contribution-subtraction lemmas in the conditional contravariant-effect note.
The first requested `prover` / `gpt-6.1-sol` / `high`; the second used the
registered defaults. Effective runtime model/effort metadata was not exposed.
The effect derivation retains the source-formation, attachment, owner/view,
consumer and fixed-valuation hypotheses; it establishes no source construction,
runtime reachability/discharge, principality or production implementation. It
does not change the reviewed conditional status. These observed launches do
not establish nested runtime capacity or hot reload.

Before publication, recheck the remote head and changed-path baselines, retain
unrelated concurrent commits, and update only the intended branch by an
expected-head fast-forward. Record the actual publication outcome in the final
report; no hypothetical worker or runtime launch is a completed action.

## Active-team CLI fallback verification (2026-10-10)

The native collaboration schema used by the primary did not expose `prover`.
The primary therefore invoked `tools/codex-prover.sh` with a bounded source-to-
proof bridge packet. Its Codex CLI session spawned `/root/bridge_proof`; the
child JSONL records `agent_role=prover`, `model=gpt-6.1-sol`, and `effort=high`.
The child wrote only
[the negative-formal live-bridge characterization](2026-10-10-contravariant-effect-live-bridge-proof.md)
and found that the frozen candidate route rejects concrete composed-negative
formal rows before they can reach the closed-filter consumer. This is a bounded
implementation reachability result, not language-level rejection or closure
of effect hygiene. A fresh compiler-referee review found no blocking/major
theorem issue and one minor handoff ambiguity; the primary repaired the wording.

The proof assignment prohibited Git commands, but the child ran read-only
`git rev-parse` and `git diff` queries. No mutation occurred; this is recorded
as workflow nonconformance and those queries are not counted as compliant
verification. The observed session demonstrates that the configured nested
CLI fallback launched a real role in this checkout; it does not promise that
future runtime environments expose the same launch surface.

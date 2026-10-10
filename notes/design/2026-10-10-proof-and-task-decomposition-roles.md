# Sol proof and task-decomposition roles

Status: Authoritative
Scope: Codex research role routing and bounded proof delegation
Approved-by: user's explicit 2026-10-10 request for these roles and delegated balance choices
Approved-at: 2026-10-10
Drafted-by: primary with GPT-6.1 Sol role/configuration audit and prompt construction
Reviewed-by: fresh independent GPT-6.1 Sol conformance/lifecycle reviewer (`role_policy_review`), 2026-10-10; no findings
Supersedes: blanket primary-only delegation only for the bounded proof-coordinator exception; no semantic or proof-status supersession

## Decision and balance

The user requested a proof specialist and a task-decomposition specialist using
GPT-6.1 Sol, with proof escalation to Astra and useful parallel work. The
existing Luna primary and specialist pins remain appropriate. The new roles
separate constructive proof work from experiments and planning from scheduling.

| Responsibility | Normal model/effort | Boundary |
|---|---|---|
| Selected primary | Existing Luna/high default | User interaction, authority, scheduling, independent review assignment, records and Git |
| `prover` | GPT-6.1 Sol/high via `[agents]` defaults | Constructive proof and exact source-to-proof bridge on leased research paths |
| `task_decomposer` | GPT-6.1 Sol/medium, pinned | Read-only proposal of a small set of concrete dependency-aware packets |
| `researcher` | Existing GPT-6.1 Sol/high default | Complementary falsification, executable models and source/artifact evidence |
| `compiler_referee` | Existing GPT-6.1 Sol/medium pin | Fresh independent closure review; never a coauthor of that proof |

Other role pins remain unchanged. The configured session ceiling stays 12;
the usual useful assignment target stays four to six, subject to the actual
runtime and aggregate compute/integration capacity.

## Executable configuration

Add `.codex/agents/prover.toml` and `.codex/agents/task-decomposer.toml` using
the existing standalone role-file format. The proof role deliberately omits
both `model` and `model_reasoning_effort`. Its ordinary defaults are exactly
`gpt-6.1-sol` / `high` from `.codex/config.toml`; an eligible native spawn can
therefore request `gpt-6-astra` / `low` without changing a role pin. Decomposition
is explicitly pinned to `gpt-6.1-sol` / `medium` and read-only.

This follows the current official [Subagents configuration](https://learn.chatgpt.com/docs/agent-configuration/subagents):
custom role-file model/effort settings override spawn values, while omitted
settings resolve from explicit spawn values, configured defaults, then the
parent. Model names in task prose do not route execution. Do not add an
unverified nesting/depth setting or claim live sessions hot-reload these files.

## Operational contract

The single detailed contract is
[Proof delegation and decomposition](../../rules/agent-orchestration.md#proof-delegation-and-decomposition).

- A leaf `prover` constructs the assigned claim and returns evidence. Only an
  explicit primary-issued proof-coordinator packet permits one additional
  generation of at most two immediate leaf workers (`prover` or `researcher`).
- The primary preallocates exact disjoint outputs, stable dependencies,
  model/effort choices and aggregate resources. Coordinators and descendants
  share the existing global budget and do not receive separate quotas.
- Normal proof leaves explicitly select Sol/high. One justified Astra leaf
  may occupy a leaf slot after a localized Sol obstruction; normally start
  low and retain the per-decision escalation limits. A model change creates
  a new bounded assignment, not a live mutation of a Sol thread.
- If nesting or override support is absent, the primary dispatches equivalent
  supported sibling packets. Report actual limitations and effective settings;
  no new user approval is needed for already-authorized work.
- The task decomposer proposes two to four useful packets, or fewer when
  justified. Already-ready work can proceed. Replanning needs a material
  change to evidence, premises or the critical path.
- Proof work retains native Simple-sub construction and propagation, lineage,
  scope, source reachability and the original theorem quantifiers. A plan,
  bounded checker or newly assumed premise does not close a proof gate.
- Producers freeze all contributing outputs and stop/reclaim leaf writes before
  integration. The primary assigns independent closure review and retains
  authority, shared coordination, question-board and Git ownership.

## Scope and verification

This change concerns agent configuration and workflow only. No compiler code,
language meaning, theorem status, test expectation or F5 cutover is changed.
Validation and independent review are recorded in the
[delivery record](../progress/2026-10-10-proof-agent-roles.md).

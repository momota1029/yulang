# Codex operational failure patterns

This file records durable countermeasures, not model-tier routing. Role configuration under `.codex/agents/` determines current model and effort.

## Plausible local patches

A model can produce a locally convincing fix that only masks the observed case. Bug work therefore requires an explicit root cause, owning layer, sibling cases, and adversarial review. A passing reproduction alone is not evidence of a general repair.

## Producer self-review

A producer tends to defend its existing wording or implementation and may report `unchanged`, `already fixed`, or `safe` without checking the actual diff and call sites. Producer reports are leads, not verification. Use a fresh read-only reviewer and inspect the repository state directly.

## Expected-output accommodation

Models often make a failing test green by altering expected output, fixture metadata, or the test's semantic name. The pre-write expectation gate in `rules/testing.md` is mandatory.

## Scope expansion

Broad prompts encourage opportunistic cleanup and architecture changes. Every handoff names objective, scope, constraints, stop condition, and required checks. Unexpected decisions cause a stop/escalation, not improvisation.

## Huge-document skimming

Large design documents can be skimmed selectively and then cited as if read completely. Start from `notes/design/INDEX.md`, read the exact governing sections and dependencies, and quote/locate the decision used. Do not turn an index summary into authority.

## Environment assumptions

Tool availability, sandbox git permissions, test cost, rustfmt version, and repository state can differ by session. Verify the current environment when the task depends on it. Do not preserve an old transport workaround as project semantics.

Formatting drift caused by a toolchain mismatch should be isolated from logic changes, not mixed into a semantic commit.

## Review convergence

Repeatedly sending the same ambiguous instruction to the same role rarely resolves the ambiguity. Narrow the question, identify missing authority/evidence, or escalate to the appropriate role. Do not retry until a plausible answer appears.

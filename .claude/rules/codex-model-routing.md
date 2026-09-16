# Codex model routing override

This project rule supersedes the `## Codex model routing policy` section in the
root `CLAUDE.md` whenever that older section describes only Sol / Terra / Luna,
treats Sol as the top tier, or otherwise conflicts with this file. All other
repository policies remain in force, including Codex-MCP-first delegation,
sandbox and approval rules, progress reporting, signed-design authority, test
safety, commit ownership, and push responsibility.

The routing order is now:

1. **Luna** for mechanical, fully specified, high-volume execution.
2. **Terra** as the default model for ordinary bounded repository work.
3. **Sol** as the normal high-judgment model for design, semantics, research,
   difficult diagnosis, and silent-failure review.
4. **Astra** only as a bounded escalation from Sol when a concrete hard point
   remains unresolved.

The purpose of this policy is not to maximize model capability on every task.
It is to preserve quality while avoiding routine Astra usage.

## Luna — mechanical work only

Use `gpt-5.6-luna` only when the correct output shape is already determined,
judgment is unnecessary, and a mechanical check catches errors cheaply. Prefer
`minimal` or `low` effort.

If the task is only one trivial edit or one command whose result shape is already
known, use the existing pass-through exception instead of delegating merely to
satisfy the MCP-first rule.

## Terra — default development tier

Use `gpt-5.6-terra` with `medium` effort by default for ordinary bounded work:
local implementation, concrete test-failure diagnosis, code navigation, focused
refactoring, and checkable multi-file edits.

Raise Terra to `high` or `xhigh` before changing model tier when the task remains
bounded and mechanically reviewable.

## Sol — normal high-judgment tier

Use `gpt-5.6-sol` for work whose main difficulty is judgment rather than volume.
Use `high` normally and `xhigh` for genuinely difficult cases.

Sol is the normal first choice for:

- architecture, public API, type-system, semantic, or performance design;
- type-soundness work and changes to shared or production-critical paths;
- open-ended investigation where the symptom is vague or cross-cutting;
- difficult compiler/runtime correctness questions;
- mathematical reasoning or proof verification;
- literature review, source comparison, novelty assessment, or research synthesis;
- drafting or restructuring durable design documents, specifications, or papers;
- independent review whose failure mode could be silent;
- difficult performance analysis where several plausible causal explanations must
  be distinguished.

These categories do **not** justify Astra by themselves. In particular, a task is
not an Astra task merely because it is important, large, architectural, a design
document, an independent review, or a type-system task. Start with Sol.

## Astra — rare bounded escalation from Sol

`gpt-6-astra` is not a standing routing tier for routine work. Use it only after
Sol has already reduced the problem to a concrete unresolved decision point.

An Astra escalation is allowed only when all of the following hold:

1. A Sol session has inspected the current evidence and produced a specific
   bottleneck, contradiction, counterexample search target, or pair of plausible
   alternatives that it cannot responsibly close.
2. The remaining uncertainty has high blast radius or a silent failure mode, and
   cannot be settled cheaply by an existing test, measurement, source lookup, or
   another bounded Sol check.
3. The Astra request is narrower than the preceding Sol task. It names the exact
   unresolved question, relevant files/evidence, and the decisive output needed.
4. The result will be reviewed or integrated by Sol/Terra afterward rather than
   turning Astra into the default implementation worker.

### Astra effort

Start Astra at `low` for a sharply bounded adjudication. Use `medium` when the
remaining point genuinely needs deeper end-to-end reasoning. Raise to `high`
only after a concrete Astra-low/medium attempt leaves a specific unresolved
problem.

Do not use Astra `xhigh` or `max` merely because those settings exist. Use them
only when the user explicitly requests that level or when a prior bounded Astra
attempt has exposed a concrete reason that additional reasoning depth is needed.

### Astra budget and fan-out

By default:

- at most **one Astra session per decision point**;
- no parallel Astra fan-out for several speculative routes;
- no repeated Astra retry with the same question and evidence;
- a second Astra call requires either a materially new bounded question produced
  by the first result or an explicit user request.

If multiple routes need exploration, explore them with Sol first and escalate
only the route whose unresolved bottleneck survives comparison.

### Tasks that do not justify Astra

Do not use Astra for:

- routine implementation after a design has been decided;
- ordinary code review or an independent second opinion when Sol found no
  concrete blocker;
- test execution, build diagnosis with a concrete symptom, formatting, migration,
  or mechanical refactoring;
- writing or polishing documentation whose content and structure are already
  decided;
- performance profiling whose next experiment is already known;
- broad repository reading merely because the repository or diff is large;
- retries caused by missing files, unclear prompts, unavailable permissions, or
  an unverified MCP capability;
- re-running the same ambiguous task without first narrowing the question.

## Escalation ladder

When a lower tier encounters work beyond its contract:

1. Luna stops and reports the non-mechanical decision point; restart on Terra.
2. Terra stops and reports the unresolved judgment; restart on Sol.
3. Sol either resolves the problem, narrows it further, or records the exact
   reason a bounded Astra escalation is justified.
4. Astra answers only that bounded hard question.
5. Return to Sol or Terra for implementation, ordinary review, checks, and
   follow-up work.

Do not jump from Terra to Astra merely because Terra struggled. Sol is the normal
intermediate judgment tier.

The user may explicitly override this ladder for a named task. A general desire
for high quality is not an override; the request must specifically ask for Astra
or for the highest available model on that task.

## Visibility before each Codex call

The existing visibility rule still applies. Before each call, state:

- selected model tier: Luna / Terra / Sol / Astra;
- selected reasoning effort;
- routing classification: `Luna opt-down`, `default Terra`, `Sol opt-up`, or
  `Astra escalation from Sol`;
- one concise reason for the selection.

For Astra, the visible note must also name the concrete Sol-discovered bottleneck
that triggered escalation.

## Required request fields

Use the actual tool-call model/effort parameters; prompt text alone does not
select the model. Include these fields in the request body for auditability:

```text
Model:
<gpt-5.6-luna | gpt-5.6-terra | gpt-5.6-sol | gpt-6-astra>

Reasoning effort:
<minimal | low | medium | high | xhigh | max>

Routing classification:
<Luna opt-down | default Terra | Sol opt-up | Astra escalation from Sol>

Routing reason:
<one concise sentence>

Astra trigger, when applicable:
<the concrete unresolved bottleneck reported by Sol>
```

Model/effort combinations must still be supported by the live Codex tool surface.
If the live schema differs from this file, report the mismatch and use the nearest
supported lower-cost setting rather than silently increasing model tier or effort.
